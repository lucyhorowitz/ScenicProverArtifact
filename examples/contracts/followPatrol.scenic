import math

param worldOffset = Vector(0, 0, 50)
param timestep = 0.1

model scenic.simulators.airsim.model

LEAD_STARTING_POS = Vector(0, 0, 10)
FOLLOW_STARTING_POS = Vector(0, 100, 10)

def magnitude(v):
    return math.hypot(v.x, v.y, v.z)


behavior Follow(target, speed=5, tolerance=2, offset=(0, 0, 1)):
    while True:
        targetPosition = target.position + offset
        velocity = targetPosition - self.position
        distance = magnitude(velocity)
        if distance > tolerance:
            velocity = (velocity / distance) * speed
            take SetVelocity(velocity)
        wait


drone1 = new Drone at LEAD_STARTING_POS,
    with behavior Patrol([(0, 0, 10), (0, 10, 10), (10, 10, 10), (10, 0, 10)], True, speed=2), with name "leader"

drone2 = new Drone at FOLLOW_STARTING_POS,
    with leadPos LEAD_STARTING_POS,
    with behavior Follow(drone1, 5, 5, (0, 0, 0)), with name "follower"

# Create/activate monitor to store leader position
monitor UpdatePosition(follower, leader):
    while True:
        follower.leadPos = leader.position
        wait

require monitor UpdatePosition(drone2, drone1)