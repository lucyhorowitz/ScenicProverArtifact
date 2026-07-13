"""Highway merge arbitration scenario.

The ego car drives in a lane blocked ahead by a slow-moving vehicle and must merge
into the adjacent lane to its left. That lane carries traffic: a gap leader ahead of
the ego and a gap follower behind it. The gap follower initially drives aggressively
(closing the gap), then yields, so a safe merge window eventually opens but the ego
may have to abort an early merge attempt.

Ground-truth gap/progress signals are computed by a monitor and stored as attributes
on the ego object, where the contract components read them as sensors.
"""
param map = localPath('../../assets/maps/CARLA/Town06.xodr')
param carla_map = 'Town06'
param render = False
model scenic.simulators.newtonian.driving_model

import math
import shapely

from scenic.core.geometry import headingOfSegment
from scenic.core.type_support import toVector

from scenic.contracts.utils import leadDistance

## Constants ##
LANE_WIDTH_EST = 3.5      # nominal lateral separation between adjacent lane centerlines
STEER_LOOKAHEAD = 10      # lookahead distance (m) for the merge steering reference
MAX_GAP = 250.0           # reported gap when no vehicle is relevant (float: sensor-typed)

# Initial longitudinal layout (all gaps in meters, measured along the road)
TOTAL_TARGET_GAP = 70                 # gap leader to gap follower separation
INIT_FRONT_GAP_MIN = 20               # ego to gap leader
INIT_FRONT_GAP_MAX = 50
OWN_LEAD_GAP = Range(30, 45)          # ego to slow car in its own lane

# Traffic speeds (m/s). The follower's cruise speed is strictly below the slow car's
# speed so the rear gap always reopens after the aggressive phase (liveness).
SLOW_CAR_SPEED = Range(2, 3)
GAP_LEADER_SPEED = Range(4.5, 6)
FOLLOWER_AGGRESSIVE_SPEED = Range(6, 8)
FOLLOWER_CRUISE_SPEED = Range(0.5, 1.5)

## Scene parameters ##
# 0 = clear, 1 = fog (degrades the rear radar)
param visibility = Discrete({0: 0.6, 1: 0.4})
# 0 = dry, 1 = overcast, 2 = rain (rain degrades the rear lidar)
param weather = Discrete({0: 0.5, 1: 0.3, 2: 0.2})
# How long the gap follower drives aggressively before yielding
param aggressive_time = Range(2, 6)

## Road selection ##
# Pick a lane section that has a same-direction lane to its left and enough road ahead.
candidate_sections = [
    sec
    for lane in network.lanes
    for sec in lane.sections
    if sec._laneToLeft is not None
    and sec._laneToLeft.isForward == sec.isForward
    and sec.lane.centerline.length > 200
]
egoSection = Uniform(*candidate_sections)
targetSection = egoSection._laneToLeft

## Behaviors ##
behavior AggressiveThenYield(aggressive_speed, cruise_speed, aggressive_time):
    do FollowLaneBehavior(target_speed=aggressive_speed) for aggressive_time seconds
    do FollowLaneBehavior(target_speed=cruise_speed)

## Vehicles ##
class EgoCar(Car):
    targetDir[dynamic, final]: float(roadDirection[self.position].yaw)

gapLeader = new Car on targetSection.centerline,
    with behavior FollowLaneBehavior(target_speed=GAP_LEADER_SPEED),
    with name "GapLeader"

gapFollower = new Car at roadDirection.followFrom(toVector(gapLeader), -TOTAL_TARGET_GAP, stepSize=0.1),
    with behavior AggressiveThenYield(
        FOLLOWER_AGGRESSIVE_SPEED,
        FOLLOWER_CRUISE_SPEED,
        globalParameters.aggressive_time),
    with name "GapFollower"

ego = new EgoCar on egoSection.centerline,
    with behavior FollowLaneBehavior(target_speed=GAP_LEADER_SPEED),
    with name "EgoCar",
    with timestep 0.1,
    with visibility float(globalParameters.visibility),
    with weather float(globalParameters.weather),
    with frontGap MAX_GAP,
    with frontGapOwn OWN_LEAD_GAP,
    with rearGap MAX_GAP,
    with rearClosing 0.0,
    with mergeProgress 0.0,
    with mergeDir 0.0

slowCar = new Car at roadDirection.followFrom(toVector(ego), OWN_LEAD_GAP, stepSize=0.1),
    with behavior FollowLaneBehavior(target_speed=SLOW_CAR_SPEED),
    with name "SlowCar"

# Keep the ego longitudinally inside the gap (Euclidean distance approximates
# along-road distance on the highway; requiring both windows, which sum to the total
# gap, forces the ego to lie between the gap leader and the gap follower).
require INIT_FRONT_GAP_MIN < (distance from ego to gapLeader) < INIT_FRONT_GAP_MAX
require (TOTAL_TARGET_GAP - INIT_FRONT_GAP_MAX) < (distance from ego to gapFollower) < (TOTAL_TARGET_GAP - INIT_FRONT_GAP_MIN)

## Ground truth signal monitor ##
monitor UpdateMergeSignals(egoCar, ownLead, gLead, gFollow, targetSec):
    tcl = targetSec.lane.centerline.lineString
    while True:
        p = shapely.Point(egoCar.position.x, egoCar.position.y)

        # Longitudinal gaps measured by arc length along the target lane centerline
        s_ego = float(shapely.line_locate_point(tcl, p))
        s_lead = float(shapely.line_locate_point(
            tcl, shapely.Point(gLead.position.x, gLead.position.y)))
        s_fol = float(shapely.line_locate_point(
            tcl, shapely.Point(gFollow.position.x, gFollow.position.y)))
        egoCar.frontGap = float(min(MAX_GAP, max(0, s_lead - s_ego)))
        egoCar.rearGap = float(min(MAX_GAP, max(0, s_ego - s_fol)))
        egoCar.rearClosing = float(gFollow.speed - egoCar.speed)

        # Gap to the slow car in the ego's own lane
        egoCar.frontGapOwn = float(leadDistance(egoCar, ownLead, network, maxDistance=MAX_GAP))

        # Lateral progress toward the target lane centerline (0 = own lane, 1 = merged)
        d_lat = float(tcl.distance(p))
        egoCar.mergeProgress = float(max(0.0, min(1.0, 1.0 - d_lat / LANE_WIDTH_EST)))

        # Steering reference: heading toward a lookahead point on the target centerline
        la = shapely.line_interpolate_point(tcl, s_ego + STEER_LOOKAHEAD)
        egoCar.mergeDir = float(headingOfSegment(
            (egoCar.position.x, egoCar.position.y), (la.x, la.y)))

        wait

require monitor UpdateMergeSignals(ego, slowCar, gapLeader, gapFollower, targetSection)

record ego.frontGap
record ego.frontGapOwn
record ego.rearGap
record ego.rearClosing
record ego.mergeProgress
record ego.mergeDir
record ego.targetDir
