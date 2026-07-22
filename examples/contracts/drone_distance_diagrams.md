# Drone-distance diagrams

These diagrams summarize the components and verification steps defined in
[`drone_distance.contract`](./drone_distance.contract).

Coverage audit: the source contains **12 component declarations**, **31 explicit
connections**, **15 contract declarations**, and **27 verification-step
statements** (including the four final `verify` statements). Every declared
component and contract is represented below. To keep the diagrams readable,
parallel `x`, `y`, and `z` connections are grouped into a single labeled arrow,
and passthrough connections at composite boundaries are not drawn as separate
nodes.

## Component containment

This tree shows the composition structure independently of signal flow.

```mermaid
flowchart TD
    F["Follower: drone2"]

    F --> SDS["SquaredDistanceSystem: sds"]
    SDS --> RPS["ReportedRelativePositionSystem: rps"]
    RPS --> GPS["GPS: gps"]
    RPS --> PRR["PositionReportReceiver: prr"]
    RPS --> RRPC["ReportedRelativePositionComputer: rrpc"]
    SDS --> SMC["SquaredMagnitudeComputer: smc"]

    F --> FCS["FollowerControlSystem: fcs"]
    FCS --> FC["FollowerController: fc"]
    FCS --> DAC["DroneActionControls: dac"]
    DAC --> VAG["VelocityActionGenerator: ag"]
    DAC --> DC["DroneControls: dc"]
```

There are no other standalone components after removal of the unused
`VelocityEstimator`.

## Component composition and data flow

```mermaid
flowchart TD
    LEAD["Lead drone position<br/><code>self.leadPos</code>"]
    SELF["Follower position<br/><code>self.position</code>"]
    VEL["Follower velocity<br/><code>self.velocity</code>"]

    subgraph FOLLOWER["Follower: drone2"]
        direction TB

        subgraph SDS["SquaredDistanceSystem: sds"]
            direction TB

            subgraph RPS["ReportedRelativePositionSystem: rps"]
                direction LR
                GPS["GPS: gps"]
                PRR["PositionReportReceiver: prr"]
                RRPC["ReportedRelativePositionComputer: rrpc"]

                GPS -- "gps_x, gps_y, gps_z" --> RRPC
                PRR -- "reported_x, reported_y, reported_z" --> RRPC
            end

            SMC["SquaredMagnitudeComputer: smc"]
            RRPC -- "rel_x, rel_y, rel_z" --> SMC
        end

        subgraph FCS["FollowerControlSystem: fcs"]
            direction TB
            FC["FollowerController: fc"]

            subgraph DAC["DroneActionControls: dac"]
                direction LR
                VAG["VelocityActionGenerator: ag"]
                DC["DroneControls: dc"]
                VAG -- "velocity_action: SetVelocity" --> DC
            end

            FC -- "cmd_vx, cmd_vy, cmd_vz" --> VAG
        end

        RRPC -- "rel_x, rel_y, rel_z" --> FC
        SMC -- "dist_sq" --> FC
    end

    SELF -- "true_pos" --> GPS
    LEAD -- "true_lead_pos" --> PRR
    DC -- "executes action" --> VEL

    classDef sensor fill:#e8f4ff,stroke:#2474a6,color:#111;
    classDef compute fill:#fff4d6,stroke:#b7791f,color:#111;
    classDef action fill:#e8f8ee,stroke:#25814b,color:#111;
    class GPS,PRR sensor;
    class RRPC,SMC,FC compute;
    class VAG,DC action;
```

The main signal path is:

```mermaid
flowchart LR
    P["Follower and leader positions"]
    R["Relative position"]
    D["Squared distance"]
    C["Velocity command"]
    A["SetVelocity action"]
    V["Follower next velocity"]

    P --> R --> D --> C --> A --> V
    R --> C
```

## Contract composition, proof, and refinement

```mermaid
flowchart TD
    GPSA["GPSAccurate<br/><b>ASSUME</b>"]
    PRRA["PositionReportReceiverAccurate<br/><b>ASSUME</b>"]
    RRPCS["ReportedRelativePositionComputerSemantics<br/><b>PROVE</b>"]
    RRRAW["Compose over rps"]
    RRPA["ReportedRelativePositionAccurate<br/><b>REFINE</b>"]

    SMCS["SquaredMagnitudeComputerSemantics<br/><b>PROVE</b>"]
    SDRAW["Compose over sds"]
    SDA["SquaredDistanceSystemAccuracy<br/><b>REFINE</b>"]

    FCS["FollowerControllerSemantics<br/><b>PROVE</b>"]
    FCDS["FollowerControllerDirectionalSafety<br/><b>REFINE</b>"]
    VA["VelocityActuation<br/><b>ASSUME</b><br/>correctness 0.99; confidence 0.999"]

    FVDSRAW["Compose over fcs"]
    FVDS["FollowerVelocityDirectionalSafety<br/><b>REFINE</b>"]
    FVSRAW["Compose over fcs"]
    FVS["FollowerVelocitySemantics<br/><b>REFINE</b>"]

    KSPRAW["Compose over drone2"]
    KSP["KeepsFollowDistanceProgress<br/><b>REFINE + VERIFY</b>"]
    KSSRAW["Compose over drone2"]
    KSS["FollowerMovementDirectionalSafety<br/><b>REFINE + VERIFY</b>"]
    NCRAW["Compose over drone2"]
    NC["NeverCrash<br/><b>REFINE + VERIFY</b>"]
    KSL["KeepsFollowDistanceLiveness<br/><b>SIMULATION TEST + VERIFY</b>"]

    GPSA --> RRRAW
    PRRA --> RRRAW
    RRPCS --> RRRAW
    RRRAW --> RRPA

    RRPA --> SDRAW
    SMCS --> SDRAW
    SDRAW --> SDA

    FCS --> FCDS
    FCDS --> FVDSRAW
    VA --> FVDSRAW
    FVDSRAW --> FVDS

    FCS --> FVSRAW
    VA --> FVSRAW
    FVSRAW --> FVS

    FVS --> KSPRAW
    SDA --> KSPRAW
    KSPRAW --> KSP

    FVDS --> KSSRAW
    SDA --> KSSRAW
    KSSRAW --> KSS

    FVS --> NCRAW
    SDA --> NCRAW
    NCRAW --> NC

    DRONE["Implemented follower: drone2"] -. "tested directly" .-> KSL

    classDef assume fill:#e8f4ff,stroke:#2474a6,color:#111;
    classDef prove fill:#fff4d6,stroke:#b7791f,color:#111;
    classDef compose fill:#f3e8ff,stroke:#8056b3,color:#111;
    classDef final fill:#e8f8ee,stroke:#25814b,stroke-width:2px,color:#111;
    class GPSA,PRRA,VA assume;
    class RRPCS,SMCS,FCS prove;
    class RRRAW,SDRAW,FVDSRAW,FVSRAW,KSPRAW,KSSRAW,NCRAW compose;
    class KSP,KSS,NC,KSL final;
```

## What the contracts establish

```mermaid
flowchart LR
    A["Accurate sensing"] --> B["Accurate relative position"]
    B --> C["Accurate squared distance"]

    D["Controller semantics"] --> E["Direction and component-speed safety"]
    D --> F["Exact commanded velocity semantics"]
    G["Velocity actuation"] --> E
    G --> F

    C --> H["Progress when too far:<br/>squared distance decreases"]
    F --> H

    C --> I["Directional safety:<br/>move toward leader when too far;<br/>away when too close"]
    E --> I

    C --> L["Collision avoidance:<br/>distance always stays above<br/>the derived positive floor"]
    F --> L

    J["End-to-end simulation"] --> K["Liveness:<br/>eventually enter max-distance band"]
```

The directional-safety and progress refinements additionally assume the position integration
law. Progress also assumes a bounded leader displacement and that the follower's
minimum approach speed exceeds the leader's maximum speed.
The collision-avoidance refinement instead uses the exact velocity semantics. It
assumes a stronger retreat gain whose radial speed beats the leader down to the
derived floor, an inactive retreat clamp, and a far-zone no-overshoot margin.
