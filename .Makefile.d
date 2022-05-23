src/EGraphList.vo src/EGraphList.glob src/EGraphList.v.beautified src/EGraphList.required_vo: src/EGraphList.v 
src/EGraphList.vio: src/EGraphList.v 
src/EGraphList.vos src/EGraphList.vok src/EGraphList.required_vos: src/EGraphList.v 
src/Enodes.vo src/Enodes.glob src/Enodes.v.beautified src/Enodes.required_vo: src/Enodes.v 
src/Enodes.vio: src/Enodes.v 
src/Enodes.vos src/Enodes.vok src/Enodes.required_vos: src/Enodes.v 
src/Congruence.vo src/Congruence.glob src/Congruence.v.beautified src/Congruence.required_vo: src/Congruence.v src/EGraphList.vo src/Enodes.vo
src/Congruence.vio: src/Congruence.v src/EGraphList.vio src/Enodes.vio
src/Congruence.vos src/Congruence.vok src/Congruence.required_vos: src/Congruence.v src/EGraphList.vos src/Enodes.vos
