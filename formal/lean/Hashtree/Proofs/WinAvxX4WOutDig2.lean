import Hashtree.Proofs.WinAvxX4WOutCells2
import Hashtree.Proofs.Avx512X16WOutBase
import Hashtree.Gen.WinAvxX4P.D203

/-! R2c windows x4 — the four digests of a tail cut from the invariant at `L204`, part 2 (generated). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)
open Hashtree.Proofs.WinAvxX4WStrip (m0WP stripKW KHs KH3s KTs KTEs)
open Hashtree.Proofs.Avx512X16WOut (OutOk)

namespace Hashtree.Proofs.WinAvxX4WOut

/-- The write log of a tail ending in `KTs` holds the 4 digests, from the invariant at `L204`. -/
theorem w4outOk_KTs (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L204) :
    OutOk inp (σ 1) 4 (mapState e σ KTs).mem := by
  have hF := hI
  have g0 := hF.1; have hF := hF.2
  have g1 := hF.1; have hF := hF.2
  have g2 := hF.1; have hF := hF.2
  have g3 := hF.1; have hF := hF.2
  have g4 := hF.1; have hF := hF.2
  have g5 := hF.1; have hF := hF.2
  have g6 := hF.1; have hF := hF.2
  have g7 := hF.1; have hF := hF.2
  have g8 := hF.1; have hF := hF.2
  have g9 := hF.1; have hF := hF.2
  have g10 := hF.1; have hF := hF.2
  have g11 := hF.1; have hF := hF.2
  have g12 := hF.1; have hF := hF.2
  have g13 := hF.1; have hF := hF.2
  have g14 := hF.1; have hF := hF.2
  have g15 := hF.1; have hF := hF.2
  have g16 := hF.1; have hF := hF.2
  have g17 := hF.1; have hF := hF.2
  have g18 := hF.1; have hF := hF.2
  have g19 := hF.1; have hF := hF.2
  have g20 := hF.1; have hF := hF.2
  have g21 := hF.1; have hF := hF.2
  have g22 := hF.1; have hF := hF.2
  have g23 := hF.1; have hF := hF.2
  have g24 := hF.1; have hF := hF.2
  have g25 := hF.1; have hF := hF.2
  have g26 := hF.1; have hF := hF.2
  have g27 := hF.1; have hF := hF.2
  have g28 := hF.1; have hF := hF.2
  have g29 := hF.1; have hF := hF.2
  have g30 := hF.1; have hF := hF.2
  have g31 := hF.1; have hF := hF.2
  have g32 := hF.1; have hF := hF.2
  have g33 := hF.1; have hF := hF.2
  have g34 := hF.1; have hF := hF.2
  have g35 := hF.1; have hF := hF.2
  have g36 := hF.1; have hF := hF.2
  have g37 := hF.1; have hF := hF.2
  have g38 := hF.1; have hF := hF.2
  have g39 := hF.1; have hF := hF.2
  have g40 := hF.1; have hF := hF.2
  have g41 := hF.1; have hF := hF.2
  have g42 := hF.1; have hF := hF.2
  have g43 := hF.1; have hF := hF.2
  have g44 := hF.1; have hF := hF.2
  have g45 := hF.1; have hF := hF.2
  have g46 := hF.1; have hF := hF.2
  have g47 := hF.1; have hF := hF.2
  have g48 := hF.1; have hF := hF.2
  have g49 := hF.1; have hF := hF.2
  have g50 := hF.1; have hF := hF.2
  have g51 := hF.1; have hF := hF.2
  have g52 := hF.1; have hF := hF.2
  have g53 := hF.1; have hF := hF.2
  have g54 := hF.1; have hF := hF.2
  have g55 := hF.1; have hF := hF.2
  have g56 := hF.1; have hF := hF.2
  have g57 := hF.1; have hF := hF.2
  have g58 := hF.1; have hF := hF.2
  have g59 := hF.1; have hF := hF.2
  have g60 := hF.1; have hF := hF.2
  have g61 := hF.1; have hF := hF.2
  have g62 := hF.1; have hF := hF.2
  have g63 := hF.1; have hF := hF.2
  have g64 := hF.1; have hF := hF.2
  have g65 := hF.1; have hF := hF.2
  have g66 := hF.1; have hF := hF.2
  have g67 := hF.1; have hF := hF.2
  have g68 := hF.1; have hF := hF.2
  have g69 := hF.1; have hF := hF.2
  have g70 := hF.1; have hF := hF.2
  have g71 := hF.1; have hF := hF.2
  have g72 := hF.1; have hF := hF.2
  have g73 := hF.1; have hF := hF.2
  have g74 := hF.1; have hF := hF.2
  have g75 := hF.1; have hF := hF.2
  have g76 := hF.1; have hF := hF.2
  have g77 := hF.1; have hF := hF.2
  have g78 := hF.1; have hF := hF.2
  have g79 := hF.1; have hF := hF.2
  have g80 := hF.1; have hF := hF.2
  have g81 := hF.1; have hF := hF.2
  have g82 := hF.1; have hF := hF.2
  have g83 := hF.1; have hF := hF.2
  have g84 := hF.1; have hF := hF.2
  have g85 := hF.1; have hF := hF.2
  have g86 := hF.1; have hF := hF.2
  have g87 := hF.1; have hF := hF.2
  have g88 := hF.1; have hF := hF.2
  have g89 := hF.1; have hF := hF.2
  have g90 := hF.1; have hF := hF.2
  have g91 := hF.1; have hF := hF.2
  have g92 := hF.1; have hF := hF.2
  have g93 := hF.1; have hF := hF.2
  have g94 := hF.1; have hF := hF.2
  have g95 := hF.1; have hF := hF.2
  have g96 := hF.1; have hF := hF.2
  have g97 := hF.1; have hF := hF.2
  have g98 := hF.1; have hF := hF.2
  have g99 := hF.1; have hF := hF.2
  have g100 := hF.1; have hF := hF.2
  have g101 := hF.1; have hF := hF.2
  have g102 := hF.1; have hF := hF.2
  have g103 := hF.1; have hF := hF.2
  have g104 := hF.1; have hF := hF.2
  have g105 := hF.1; have hF := hF.2
  have g106 := hF.1; have hF := hF.2
  have g107 := hF.1; have hF := hF.2
  have g108 := hF.1; have hF := hF.2
  have g109 := hF.1; have hF := hF.2
  have g110 := hF.1; have hF := hF.2
  have g111 := hF.1; have hF := hF.2
  have g112 := hF.1; have hF := hF.2
  have g113 := hF.1; have hF := hF.2
  have g114 := hF.1; have hF := hF.2
  have g115 := hF.1; have hF := hF.2
  have g116 := hF.1; have hF := hF.2
  have g117 := hF.1; have hF := hF.2
  have g118 := hF.1; have hF := hF.2
  have g119 := hF.1; have hF := hF.2
  have g120 := hF.1; have hF := hF.2
  have g121 := hF.1; have hF := hF.2
  have g122 := hF.1; have hF := hF.2
  have g123 := hF.1; have hF := hF.2
  have g124 := hF.1; have hF := hF.2
  have g125 := hF.1; have hF := hF.2
  have g126 := hF.1; have hF := hF.2
  have g127 := hF.1; have hF := hF.2
  have g128 := hF.1; have hF := hF.2
  have g129 := hF.1; have hF := hF.2
  have g130 := hF.1; have hF := hF.2
  have g131 := hF.1; have hF := hF.2
  have g132 := hF.1; have hF := hF.2
  have g133 := hF.1; have hF := hF.2
  have g134 := hF.1; have hF := hF.2
  have g135 := hF.1; have hF := hF.2
  have g136 := hF.1; have hF := hF.2
  have g137 := hF.1; have hF := hF.2
  have g138 := hF.1; have hF := hF.2
  have g139 := hF.1; have hF := hF.2
  have g140 := hF.1; have hF := hF.2
  have g141 := hF.1; have hF := hF.2
  have g142 := hF.1; have hF := hF.2
  have g143 := hF.1; have hF := hF.2
  have g144 := hF.1; have hF := hF.2
  have g145 := hF.1; have hF := hF.2
  have g146 := hF.1; have hF := hF.2
  have g147 := hF.1; have hF := hF.2
  have g148 := hF.1; have hF := hF.2
  have g149 := hF.1; have hF := hF.2
  have g150 := hF.1; have hF := hF.2
  have g151 := hF.1; have hF := hF.2
  have g152 := hF.1; have hF := hF.2
  have g153 := hF.1; have hF := hF.2
  have g154 := hF.1; have hF := hF.2
  have g155 := hF.1; have hF := hF.2
  have g156 := hF.1; have hF := hF.2
  have g157 := hF.1; have hF := hF.2
  have g158 := hF.1; have hF := hF.2
  have g159 := hF.1; have hF := hF.2
  have g160 := hF.1; have hF := hF.2
  have g161 := hF.1; have hF := hF.2
  have g162 := hF.1; have hF := hF.2
  have g163 := hF.1; have hF := hF.2
  have g164 := hF.1; have hF := hF.2
  have g165 := hF.1; have hF := hF.2
  have g166 := hF.1; have hF := hF.2
  have g167 := hF.1; have hF := hF.2
  have g168 := hF.1; have hF := hF.2
  have g169 := hF.1; have hF := hF.2
  have g170 := hF.1; have hF := hF.2
  have g171 := hF.1; have hF := hF.2
  have g172 := hF.1; have hF := hF.2
  have g173 := hF.1; have hF := hF.2
  have g174 := hF.1; have hF := hF.2
  have g175 := hF.1; have hF := hF.2
  have g176 := hF.1; have hF := hF.2
  have g177 := hF.1; have hF := hF.2
  have g178 := hF.1; have hF := hF.2
  have g179 := hF.1; have hF := hF.2
  have g180 := hF.1; have hF := hF.2
  have g181 := hF.1; have hF := hF.2
  have g182 := hF.1; have hF := hF.2
  have g183 := hF.1; have hF := hF.2
  have g184 := hF.1; have hF := hF.2
  have g185 := hF.1; have hF := hF.2
  have g186 := hF.1; have hF := hF.2
  have g187 := hF.1; have hF := hF.2
  have g188 := hF.1; have hF := hF.2
  have g189 := hF.1; have hF := hF.2
  have g190 := hF.1; have hF := hF.2
  have g191 := hF.1; have hF := hF.2
  have g192 := hF.1; have hF := hF.2
  have g193 := hF.1; have hF := hF.2
  have g194 := hF.1; have hF := hF.2
  have g195 := hF.1; have hF := hF.2
  have g196 := hF.1; have hF := hF.2
  have g197 := hF.1; have hF := hF.2
  have g198 := hF.1; have hF := hF.2
  have g199 := hF.1; have hF := hF.2
  have g200 := hF.1; have hF := hF.2
  have g201 := hF.1; have hF := hF.2
  have g202 := hF.1; have hF := hF.2
  have g203 := hF.1; have hF := hF.2
  have g204 := hF.1; have hF := hF.2
  have g205 := hF.1; have hF := hF.2
  have g206 := hF.1; have hF := hF.2
  have g207 := hF.1; have hF := hF.2
  have g208 := hF.1; have hF := hF.2
  have g209 := hF.1; have hF := hF.2
  have g210 := hF.1; have hF := hF.2
  have g211 := hF.1; have hF := hF.2
  have g212 := hF.1; have hF := hF.2
  have g213 := hF.1; have hF := hF.2
  have g214 := hF.1; have hF := hF.2
  have g215 := hF.1; have hF := hF.2
  have g216 := hF.1; have hF := hF.2
  have g217 := hF.1; have hF := hF.2
  have g218 := hF.1; have hF := hF.2
  have g219 := hF.1; have hF := hF.2
  have g220 := hF.1; have hF := hF.2
  have g221 := hF.1; have hF := hF.2
  have g222 := hF.1; have hF := hF.2
  have g223 := hF.1; have hF := hF.2
  have g224 := hF.1; have hF := hF.2
  have g225 := hF.1; have hF := hF.2
  have g226 := hF.1; have hF := hF.2
  have g227 := hF.1; have hF := hF.2
  have g228 := hF.1; have hF := hF.2
  have g229 := hF.1; have hF := hF.2
  have g230 := hF.1; have hF := hF.2
  have g231 := hF.1; have hF := hF.2
  have g232 := hF.1; have hF := hF.2
  have g233 := hF.1; have hF := hF.2
  have g234 := hF.1; have hF := hF.2
  have g235 := hF.1; have hF := hF.2
  have g236 := hF.1; have hF := hF.2
  have g237 := hF.1; have hF := hF.2
  have g238 := hF.1; have hF := hF.2
  have g239 := hF.1; have hF := hF.2
  have g240 := hF.1; have hF := hF.2
  have g241 := hF.1; have hF := hF.2
  have g242 := hF.1; have hF := hF.2
  have g243 := hF.1; have hF := hF.2
  have g244 := hF.1; have hF := hF.2
  have g245 := hF.1; have hF := hF.2
  have g246 := hF.1; have hF := hF.2
  have g247 := hF.1; have hF := hF.2
  have g248 := hF.1; have hF := hF.2
  have g249 := hF.1; have hF := hF.2
  have g250 := hF.1; have hF := hF.2
  have g251 := hF.1; have hF := hF.2
  have g252 := hF.1; have hF := hF.2
  have g253 := hF.1; have hF := hF.2
  have g254 := hF.1; have hF := hF.2
  have g255 := hF.1; have hF := hF.2
  have g256 := hF.1; have hF := hF.2
  have g257 := hF.1; have hF := hF.2
  have g258 := hF.1; have hF := hF.2
  have g259 := hF.1; have hF := hF.2
  have g260 := hF.1; have hF := hF.2
  have g261 := hF.1; have hF := hF.2
  have g262 := hF.1; have hF := hF.2
  have g263 := hF.1; have hF := hF.2
  have g264 := hF.1; have hF := hF.2
  have g265 := hF.1; have hF := hF.2
  have g266 := hF.1; have hF := hF.2
  have g267 := hF.1; have hF := hF.2
  have g268 := hF.1; have hF := hF.2
  have g269 := hF.1; have hF := hF.2
  have g270 := hF.1; have hF := hF.2
  have g271 := hF.1; have hF := hF.2
  have g272 := hF.1; have hF := hF.2
  have g273 := hF.1; have hF := hF.2
  have g274 := hF.1; have hF := hF.2
  have g275 := hF.1; have hF := hF.2
  have g276 := hF.1; have hF := hF.2
  have g277 := hF.1; have hF := hF.2
  have g278 := hF.1; have hF := hF.2
  have g279 := hF.1; have hF := hF.2
  have g280 := hF.1; have hF := hF.2
  have g281 := hF.1; have hF := hF.2
  have g282 := hF.1; have hF := hF.2
  have g283 := hF.1; have hF := hF.2
  have g284 := hF.1; have hF := hF.2
  have g285 := hF.1; have hF := hF.2
  have g286 := hF.1; have hF := hF.2
  have g287 := hF.1; have hF := hF.2
  have g288 := hF.1; have hF := hF.2
  have g289 := hF.1; have hF := hF.2
  have g290 := hF.1; have hF := hF.2
  have g291 := hF.1; have hF := hF.2
  have g292 := hF.1; have hF := hF.2
  have g293 := hF.1; have hF := hF.2
  have g294 := hF.1; have hF := hF.2
  have g295 := hF.1; have hF := hF.2
  have g296 := hF.1; have hF := hF.2
  have g297 := hF.1; have hF := hF.2
  have g298 := hF.1; have hF := hF.2
  have g299 := hF.1; have hF := hF.2
  have g300 := hF.1; have hF := hF.2
  have g301 := hF.1; have hF := hF.2
  have g302 := hF.1; have hF := hF.2
  have g303 := hF.1; have hF := hF.2
  have g304 := hF.1; have hF := hF.2
  have g305 := hF.1; have hF := hF.2
  have g306 := hF.1; have hF := hF.2
  have g307 := hF.1; have hF := hF.2
  have g308 := hF.1; have hF := hF.2
  have g309 := hF.1; have hF := hF.2
  have g310 := hF.1; have hF := hF.2
  have g311 := hF.1; have hF := hF.2
  have g312 := hF.1; have hF := hF.2
  have g313 := hF.1; have hF := hF.2
  have g314 := hF.1; have hF := hF.2
  have g315 := hF.1; have hF := hF.2
  have g316 := hF.1; have hF := hF.2
  have g317 := hF.1; have hF := hF.2
  have g318 := hF.1; have hF := hF.2
  have g319 := hF.1; have hF := hF.2
  have g320 := hF.1; have hF := hF.2
  have g321 := hF.1; have hF := hF.2
  have g322 := hF.1; have hF := hF.2
  have g323 := hF.1; have hF := hF.2
  have g324 := hF.1; have hF := hF.2
  have g325 := hF.1; have hF := hF.2
  have g326 := hF.1; have hF := hF.2
  have g327 := hF.1; have hF := hF.2
  have g328 := hF.1; have hF := hF.2
  have g329 := hF.1; have hF := hF.2
  have g330 := hF.1; have hF := hF.2
  have g331 := hF.1; have hF := hF.2
  have g332 := hF.1; have hF := hF.2
  have g333 := hF.1; have hF := hF.2
  have g334 := hF.1; have hF := hF.2
  have g335 := hF.1; have hF := hF.2
  have g336 := hF.1; have hF := hF.2
  have g337 := hF.1; have hF := hF.2
  have g338 := hF.1; have hF := hF.2
  have g339 := hF.1; have hF := hF.2
  have g340 := hF.1; have hF := hF.2
  have g341 := hF.1; have hF := hF.2
  have g342 := hF.1; have hF := hF.2
  have g343 := hF.1; have hF := hF.2
  have g344 := hF.1; have hF := hF.2
  have g345 := hF.1; have hF := hF.2
  have g346 := hF.1; have hF := hF.2
  have g347 := hF.1; have hF := hF.2
  have g348 := hF.1; have hF := hF.2
  have g349 := hF.1; have hF := hF.2
  have g350 := hF.1; have hF := hF.2
  have g351 := hF.1; have hF := hF.2
  have g352 := hF.1; have hF := hF.2
  have g353 := hF.1; have hF := hF.2
  have g354 := hF.1; have hF := hF.2
  have g355 := hF.1; have hF := hF.2
  have g356 := hF.1; have hF := hF.2
  have g357 := hF.1; have hF := hF.2
  have g358 := hF.1; have hF := hF.2
  have g359 := hF.1; have hF := hF.2
  have g360 := hF.1; have hF := hF.2
  have g361 := hF.1; have hF := hF.2
  have g362 := hF.1; have hF := hF.2
  have g363 := hF.1; have hF := hF.2
  have g364 := hF.1; have hF := hF.2
  have g365 := hF.1; have hF := hF.2
  have g366 := hF.1; have hF := hF.2
  have g367 := hF.1; have hF := hF.2
  have g368 := hF.1; have hF := hF.2
  have g369 := hF.1; have hF := hF.2
  have g370 := hF.1; have hF := hF.2
  have g371 := hF.1; have hF := hF.2
  have g372 := hF.1; have hF := hF.2
  have g373 := hF.1; have hF := hF.2
  have g374 := hF.1; have hF := hF.2
  have g375 := hF.1; have hF := hF.2
  have g376 := hF.1; have hF := hF.2
  have g377 := hF.1; have hF := hF.2
  have g378 := hF.1; have hF := hF.2
  have g379 := hF.1; have hF := hF.2
  have g380 := hF.1; have hF := hF.2
  have g381 := hF.1; have hF := hF.2
  have g382 := hF.1; have hF := hF.2
  have g383 := hF.1; have hF := hF.2
  have g384 := hF.1; have hF := hF.2
  have g385 := hF.1; have hF := hF.2
  have g386 := hF.1; have hF := hF.2
  have g387 := hF.1; have hF := hF.2
  have g388 := hF.1; have hF := hF.2
  have g389 := hF.1; have hF := hF.2
  have g390 := hF.1; have hF := hF.2
  have g391 := hF.1; have hF := hF.2
  have g392 := hF.1; have hF := hF.2
  have g393 := hF.1; have hF := hF.2
  have g394 := hF.1; have hF := hF.2
  have g395 := hF.1; have hF := hF.2
  have g396 := hF.1; have hF := hF.2
  have g397 := hF.1; have hF := hF.2
  have g398 := hF.1; have hF := hF.2
  have g399 := hF.1; have hF := hF.2
  have g400 := hF.1; have hF := hF.2
  have g401 := hF.1; have hF := hF.2
  have g402 := hF.1; have hF := hF.2
  have g403 := hF.1; have hF := hF.2
  have g404 := hF.1; have hF := hF.2
  have g405 := hF.1; have hF := hF.2
  have g406 := hF.1; have hF := hF.2
  have g407 := hF.1; have hF := hF.2
  have g408 := hF.1; have hF := hF.2
  have g409 := hF.1; have hF := hF.2
  have g410 := hF.1; have hF := hF.2
  have g411 := hF.1; have hF := hF.2
  have g412 := hF.1; have hF := hF.2
  have g413 := hF.1; have hF := hF.2
  have g414 := hF.1; have hF := hF.2
  have g415 := hF.1; have hF := hF.2
  have g416 := hF.1; have hF := hF.2
  have g417 := hF.1; have hF := hF.2
  have g418 := hF.1; have hF := hF.2
  have g419 := hF.1; have hF := hF.2
  have g420 := hF.1; have hF := hF.2
  have g421 := hF.1; have hF := hF.2
  have g422 := hF.1; have hF := hF.2
  have g423 := hF.1; have hF := hF.2
  have g424 := hF.1; have hF := hF.2
  have g425 := hF.1; have hF := hF.2
  have g426 := hF.1; have hF := hF.2
  have g427 := hF.1; have hF := hF.2
  have g428 := hF.1; have hF := hF.2
  have g429 := hF.1; have hF := hF.2
  have g430 := hF.1; have hF := hF.2
  have g431 := hF.1; have hF := hF.2
  have g432 := hF.1; have hF := hF.2
  have g433 := hF.1; have hF := hF.2
  have g434 := hF.1; have hF := hF.2
  have g435 := hF.1; have hF := hF.2
  have g436 := hF.1; have hF := hF.2
  have g437 := hF.1; have hF := hF.2
  have g438 := hF.1; have hF := hF.2
  have g439 := hF.1; have hF := hF.2
  have g440 := hF.1; have hF := hF.2
  have g441 := hF.1; have hF := hF.2
  have g442 := hF.1; have hF := hF.2
  have g443 := hF.1; have hF := hF.2
  have g444 := hF.1; have hF := hF.2
  have g445 := hF.1; have hF := hF.2
  have g446 := hF.1; have hF := hF.2
  have g447 := hF.1; have hF := hF.2
  have g448 := hF.1; have hF := hF.2
  have g449 := hF.1; have hF := hF.2
  have g450 := hF.1; have hF := hF.2
  have g451 := hF.1; have hF := hF.2
  have g452 := hF.1; have hF := hF.2
  have g453 := hF.1; have hF := hF.2
  have g454 := hF.1; have hF := hF.2
  have g455 := hF.1; have hF := hF.2
  have g456 := hF.1; have hF := hF.2
  have g457 := hF.1; have hF := hF.2
  have g458 := hF.1; have hF := hF.2
  have g459 := hF.1; have hF := hF.2
  have g460 := hF.1; have hF := hF.2
  have g461 := hF.1; have hF := hF.2
  have g462 := hF.1; have hF := hF.2
  have g463 := hF.1; have hF := hF.2
  have g464 := hF.1; have hF := hF.2
  have g465 := hF.1; have hF := hF.2
  have g466 := hF.1; have hF := hF.2
  have g467 := hF.1; have hF := hF.2
  have g468 := hF.1; have hF := hF.2
  have g469 := hF.1; have hF := hF.2
  have g470 := hF.1; have hF := hF.2
  have g471 := hF.1; have hF := hF.2
  have g472 := hF.1; have hF := hF.2
  have g473 := hF.1; have hF := hF.2
  have g474 := hF.1; have hF := hF.2
  have g475 := hF.1; have hF := hF.2
  have g476 := hF.1; have hF := hF.2
  have g477 := hF.1; have hF := hF.2
  have g478 := hF.1; have hF := hF.2
  have g479 := hF.1; have hF := hF.2
  have g480 := hF.1; have hF := hF.2
  have g481 := hF.1; have hF := hF.2
  have g482 := hF.1; have hF := hF.2
  have g483 := hF.1; have hF := hF.2
  have g484 := hF.1; have hF := hF.2
  have g485 := hF.1; have hF := hF.2
  have g486 := hF.1; have hF := hF.2
  have g487 := hF.1; have hF := hF.2
  have g488 := hF.1; have hF := hF.2
  have g489 := hF.1; have hF := hF.2
  have g490 := hF.1; have hF := hF.2
  have g491 := hF.1; have hF := hF.2
  have g492 := hF.1; have hF := hF.2
  have g493 := hF.1; have hF := hF.2
  have g494 := hF.1; have hF := hF.2
  have g495 := hF.1; have hF := hF.2
  have g496 := hF.1; have hF := hF.2
  have g497 := hF.1; have hF := hF.2
  have g498 := hF.1; have hF := hF.2
  have g499 := hF.1; have hF := hF.2
  have g500 := hF.1; have hF := hF.2
  have g501 := hF.1; have hF := hF.2
  have g502 := hF.1; have hF := hF.2
  have g503 := hF.1; have hF := hF.2
  have g504 := hF.1; have hF := hF.2
  have g505 := hF.1; have hF := hF.2
  have g506 := hF.1; have hF := hF.2
  have g507 := hF.1; have hF := hF.2
  have g508 := hF.1; have hF := hF.2
  have g509 := hF.1; have hF := hF.2
  have g510 := hF.1; have hF := hF.2
  have g511 := hF.1; have hF := hF.2
  have g512 := hF.1; have hF := hF.2
  have g513 := hF.1; have hF := hF.2
  have g514 := hF.1; have hF := hF.2
  have g515 := hF.1; have hF := hF.2
  have g516 := hF.1; have hF := hF.2
  have g517 := hF.1; have hF := hF.2
  have g518 := hF.1; have hF := hF.2
  have g519 := hF.1; have hF := hF.2
  have g520 := hF.1; have hF := hF.2
  have g521 := hF.1; have hF := hF.2
  have g522 := hF.1; have hF := hF.2
  have g523 := hF.1; have hF := hF.2
  have g524 := hF.1; have hF := hF.2
  have g525 := hF.1; have hF := hF.2
  have g526 := hF.1; have hF := hF.2
  have g527 := hF.1; have hF := hF.2
  have g528 := hF.1; have hF := hF.2
  have g529 := hF.1; have hF := hF.2
  have g530 := hF.1; have hF := hF.2
  have g531 := hF.1; have hF := hF.2
  have g532 := hF.1; have hF := hF.2
  have g533 := hF.1; have hF := hF.2
  have g534 := hF.1; have hF := hF.2
  have g535 := hF.1; have hF := hF.2
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨e (.n 1127), outCell_sound _ σ KTs 0 1127 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1127) = qv inp (.HB 0 0) from g384,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨e (.n 1126), outCell_sound _ σ KTs 1 1126 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1126) = qv inp (.HB 0 0) from g385,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨e (.n 1125), outCell_sound _ σ KTs 2 1125 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1125) = qv inp (.HB 0 0) from g386,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨e (.n 1124), outCell_sound _ σ KTs 3 1124 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1124) = qv inp (.HB 0 0) from g387,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨e (.n 1123), outCell_sound _ σ KTs 4 1123 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1123) = qv inp (.HB 0 1) from g388,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨e (.n 1122), outCell_sound _ σ KTs 5 1122 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1122) = qv inp (.HB 0 1) from g389,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨e (.n 1121), outCell_sound _ σ KTs 6 1121 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1121) = qv inp (.HB 0 1) from g390,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨e (.n 1120), outCell_sound _ σ KTs 7 1120 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1120) = qv inp (.HB 0 1) from g391,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨e (.n 1119), outCell_sound _ σ KTs 8 1119 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1119) = qv inp (.HB 0 2) from g392,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨e (.n 1118), outCell_sound _ σ KTs 9 1118 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1118) = qv inp (.HB 0 2) from g393,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨e (.n 1117), outCell_sound _ σ KTs 10 1117 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1117) = qv inp (.HB 0 2) from g394,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨e (.n 1116), outCell_sound _ σ KTs 11 1116 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1116) = qv inp (.HB 0 2) from g395,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨e (.n 1115), outCell_sound _ σ KTs 12 1115 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1115) = qv inp (.HB 0 3) from g396,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨e (.n 1114), outCell_sound _ σ KTs 13 1114 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1114) = qv inp (.HB 0 3) from g397,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨e (.n 1113), outCell_sound _ σ KTs 14 1113 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1113) = qv inp (.HB 0 3) from g398,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨e (.n 1112), outCell_sound _ σ KTs 15 1112 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1112) = qv inp (.HB 0 3) from g399,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨e (.n 1111), outCell_sound _ σ KTs 16 1111 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1111) = qv inp (.HB 0 4) from g400,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨e (.n 1110), outCell_sound _ σ KTs 17 1110 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1110) = qv inp (.HB 0 4) from g401,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨e (.n 1109), outCell_sound _ σ KTs 18 1109 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1109) = qv inp (.HB 0 4) from g402,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨e (.n 1108), outCell_sound _ σ KTs 19 1108 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1108) = qv inp (.HB 0 4) from g403,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨e (.n 1107), outCell_sound _ σ KTs 20 1107 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1107) = qv inp (.HB 0 5) from g404,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨e (.n 1106), outCell_sound _ σ KTs 21 1106 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1106) = qv inp (.HB 0 5) from g405,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨e (.n 1105), outCell_sound _ σ KTs 22 1105 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1105) = qv inp (.HB 0 5) from g406,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨e (.n 1104), outCell_sound _ σ KTs 23 1104 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1104) = qv inp (.HB 0 5) from g407,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨e (.n 1103), outCell_sound _ σ KTs 24 1103 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1103) = qv inp (.HB 0 6) from g408,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨e (.n 1102), outCell_sound _ σ KTs 25 1102 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1102) = qv inp (.HB 0 6) from g409,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨e (.n 1101), outCell_sound _ σ KTs 26 1101 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1101) = qv inp (.HB 0 6) from g410,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨e (.n 1100), outCell_sound _ σ KTs 27 1100 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1100) = qv inp (.HB 0 6) from g411,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨e (.n 1099), outCell_sound _ σ KTs 28 1099 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1099) = qv inp (.HB 0 7) from g412,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨e (.n 1098), outCell_sound _ σ KTs 29 1098 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1098) = qv inp (.HB 0 7) from g413,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨e (.n 1097), outCell_sound _ σ KTs 30 1097 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1097) = qv inp (.HB 0 7) from g414,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨e (.n 1096), outCell_sound _ σ KTs 31 1096 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1096) = qv inp (.HB 0 7) from g415,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨e (.n 1095), outCell_sound _ σ KTs 32 1095 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1095) = qv inp (.HB 1 0) from g416,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨e (.n 1094), outCell_sound _ σ KTs 33 1094 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1094) = qv inp (.HB 1 0) from g417,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨e (.n 1093), outCell_sound _ σ KTs 34 1093 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1093) = qv inp (.HB 1 0) from g418,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨e (.n 1092), outCell_sound _ σ KTs 35 1092 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1092) = qv inp (.HB 1 0) from g419,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨e (.n 1091), outCell_sound _ σ KTs 36 1091 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1091) = qv inp (.HB 1 1) from g420,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨e (.n 1090), outCell_sound _ σ KTs 37 1090 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1090) = qv inp (.HB 1 1) from g421,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨e (.n 1089), outCell_sound _ σ KTs 38 1089 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1089) = qv inp (.HB 1 1) from g422,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨e (.n 1088), outCell_sound _ σ KTs 39 1088 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1088) = qv inp (.HB 1 1) from g423,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨e (.n 1087), outCell_sound _ σ KTs 40 1087 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1087) = qv inp (.HB 1 2) from g424,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨e (.n 1086), outCell_sound _ σ KTs 41 1086 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1086) = qv inp (.HB 1 2) from g425,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨e (.n 1085), outCell_sound _ σ KTs 42 1085 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1085) = qv inp (.HB 1 2) from g426,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨e (.n 1084), outCell_sound _ σ KTs 43 1084 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1084) = qv inp (.HB 1 2) from g427,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨e (.n 1083), outCell_sound _ σ KTs 44 1083 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1083) = qv inp (.HB 1 3) from g428,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨e (.n 1082), outCell_sound _ σ KTs 45 1082 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1082) = qv inp (.HB 1 3) from g429,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨e (.n 1081), outCell_sound _ σ KTs 46 1081 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1081) = qv inp (.HB 1 3) from g430,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨e (.n 1080), outCell_sound _ σ KTs 47 1080 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1080) = qv inp (.HB 1 3) from g431,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨e (.n 1079), outCell_sound _ σ KTs 48 1079 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1079) = qv inp (.HB 1 4) from g432,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨e (.n 1078), outCell_sound _ σ KTs 49 1078 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1078) = qv inp (.HB 1 4) from g433,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨e (.n 1077), outCell_sound _ σ KTs 50 1077 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1077) = qv inp (.HB 1 4) from g434,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨e (.n 1076), outCell_sound _ σ KTs 51 1076 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1076) = qv inp (.HB 1 4) from g435,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨e (.n 1075), outCell_sound _ σ KTs 52 1075 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1075) = qv inp (.HB 1 5) from g436,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨e (.n 1074), outCell_sound _ σ KTs 53 1074 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1074) = qv inp (.HB 1 5) from g437,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨e (.n 1073), outCell_sound _ σ KTs 54 1073 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1073) = qv inp (.HB 1 5) from g438,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨e (.n 1072), outCell_sound _ σ KTs 55 1072 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1072) = qv inp (.HB 1 5) from g439,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨e (.n 1071), outCell_sound _ σ KTs 56 1071 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1071) = qv inp (.HB 1 6) from g440,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨e (.n 1070), outCell_sound _ σ KTs 57 1070 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1070) = qv inp (.HB 1 6) from g441,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨e (.n 1069), outCell_sound _ σ KTs 58 1069 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1069) = qv inp (.HB 1 6) from g442,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨e (.n 1068), outCell_sound _ σ KTs 59 1068 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1068) = qv inp (.HB 1 6) from g443,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨e (.n 1067), outCell_sound _ σ KTs 60 1067 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1067) = qv inp (.HB 1 7) from g444,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨e (.n 1066), outCell_sound _ σ KTs 61 1066 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1066) = qv inp (.HB 1 7) from g445,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨e (.n 1065), outCell_sound _ σ KTs 62 1065 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1065) = qv inp (.HB 1 7) from g446,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨e (.n 1064), outCell_sound _ σ KTs 63 1064 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1064) = qv inp (.HB 1 7) from g447,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨e (.n 1063), outCell_sound _ σ KTs 64 1063 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1063) = qv inp (.HB 2 0) from g448,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨e (.n 1062), outCell_sound _ σ KTs 65 1062 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1062) = qv inp (.HB 2 0) from g449,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨e (.n 1061), outCell_sound _ σ KTs 66 1061 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1061) = qv inp (.HB 2 0) from g450,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨e (.n 1060), outCell_sound _ σ KTs 67 1060 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1060) = qv inp (.HB 2 0) from g451,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨e (.n 1059), outCell_sound _ σ KTs 68 1059 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1059) = qv inp (.HB 2 1) from g452,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨e (.n 1058), outCell_sound _ σ KTs 69 1058 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1058) = qv inp (.HB 2 1) from g453,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨e (.n 1057), outCell_sound _ σ KTs 70 1057 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1057) = qv inp (.HB 2 1) from g454,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨e (.n 1056), outCell_sound _ σ KTs 71 1056 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1056) = qv inp (.HB 2 1) from g455,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨e (.n 1055), outCell_sound _ σ KTs 72 1055 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1055) = qv inp (.HB 2 2) from g456,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨e (.n 1054), outCell_sound _ σ KTs 73 1054 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1054) = qv inp (.HB 2 2) from g457,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨e (.n 1053), outCell_sound _ σ KTs 74 1053 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1053) = qv inp (.HB 2 2) from g458,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨e (.n 1052), outCell_sound _ σ KTs 75 1052 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1052) = qv inp (.HB 2 2) from g459,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨e (.n 1051), outCell_sound _ σ KTs 76 1051 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1051) = qv inp (.HB 2 3) from g460,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨e (.n 1050), outCell_sound _ σ KTs 77 1050 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1050) = qv inp (.HB 2 3) from g461,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨e (.n 1049), outCell_sound _ σ KTs 78 1049 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1049) = qv inp (.HB 2 3) from g462,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨e (.n 1048), outCell_sound _ σ KTs 79 1048 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1048) = qv inp (.HB 2 3) from g463,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨e (.n 1047), outCell_sound _ σ KTs 80 1047 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1047) = qv inp (.HB 2 4) from g464,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨e (.n 1046), outCell_sound _ σ KTs 81 1046 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1046) = qv inp (.HB 2 4) from g465,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨e (.n 1045), outCell_sound _ σ KTs 82 1045 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1045) = qv inp (.HB 2 4) from g466,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨e (.n 1044), outCell_sound _ σ KTs 83 1044 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1044) = qv inp (.HB 2 4) from g467,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨e (.n 1043), outCell_sound _ σ KTs 84 1043 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1043) = qv inp (.HB 2 5) from g468,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨e (.n 1042), outCell_sound _ σ KTs 85 1042 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1042) = qv inp (.HB 2 5) from g469,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨e (.n 1041), outCell_sound _ σ KTs 86 1041 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1041) = qv inp (.HB 2 5) from g470,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨e (.n 1040), outCell_sound _ σ KTs 87 1040 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1040) = qv inp (.HB 2 5) from g471,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨e (.n 1039), outCell_sound _ σ KTs 88 1039 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1039) = qv inp (.HB 2 6) from g472,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨e (.n 1038), outCell_sound _ σ KTs 89 1038 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1038) = qv inp (.HB 2 6) from g473,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨e (.n 1037), outCell_sound _ σ KTs 90 1037 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1037) = qv inp (.HB 2 6) from g474,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨e (.n 1036), outCell_sound _ σ KTs 91 1036 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1036) = qv inp (.HB 2 6) from g475,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨e (.n 1035), outCell_sound _ σ KTs 92 1035 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1035) = qv inp (.HB 2 7) from g476,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨e (.n 1034), outCell_sound _ σ KTs 93 1034 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1034) = qv inp (.HB 2 7) from g477,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨e (.n 1033), outCell_sound _ σ KTs 94 1033 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1033) = qv inp (.HB 2 7) from g478,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨e (.n 1032), outCell_sound _ σ KTs 95 1032 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1032) = qv inp (.HB 2 7) from g479,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨e (.n 1031), outCell_sound _ σ KTs 96 1031 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1031) = qv inp (.HB 3 0) from g480,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨e (.n 1030), outCell_sound _ σ KTs 97 1030 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1030) = qv inp (.HB 3 0) from g481,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨e (.n 1029), outCell_sound _ σ KTs 98 1029 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1029) = qv inp (.HB 3 0) from g482,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨e (.n 1028), outCell_sound _ σ KTs 99 1028 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1028) = qv inp (.HB 3 0) from g483,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨e (.n 1027), outCell_sound _ σ KTs 100 1027 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1027) = qv inp (.HB 3 1) from g484,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨e (.n 1026), outCell_sound _ σ KTs 101 1026 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1026) = qv inp (.HB 3 1) from g485,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨e (.n 1025), outCell_sound _ σ KTs 102 1025 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1025) = qv inp (.HB 3 1) from g486,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨e (.n 1024), outCell_sound _ σ KTs 103 1024 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1024) = qv inp (.HB 3 1) from g487,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨e (.n 1023), outCell_sound _ σ KTs 104 1023 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1023) = qv inp (.HB 3 2) from g488,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨e (.n 1022), outCell_sound _ σ KTs 105 1022 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1022) = qv inp (.HB 3 2) from g489,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨e (.n 1021), outCell_sound _ σ KTs 106 1021 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1021) = qv inp (.HB 3 2) from g490,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨e (.n 1020), outCell_sound _ σ KTs 107 1020 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1020) = qv inp (.HB 3 2) from g491,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨e (.n 1019), outCell_sound _ σ KTs 108 1019 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1019) = qv inp (.HB 3 3) from g492,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨e (.n 1018), outCell_sound _ σ KTs 109 1018 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1018) = qv inp (.HB 3 3) from g493,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨e (.n 1017), outCell_sound _ σ KTs 110 1017 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1017) = qv inp (.HB 3 3) from g494,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨e (.n 1016), outCell_sound _ σ KTs 111 1016 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1016) = qv inp (.HB 3 3) from g495,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨e (.n 1015), outCell_sound _ σ KTs 112 1015 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1015) = qv inp (.HB 3 4) from g496,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨e (.n 1014), outCell_sound _ σ KTs 113 1014 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1014) = qv inp (.HB 3 4) from g497,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨e (.n 1013), outCell_sound _ σ KTs 114 1013 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1013) = qv inp (.HB 3 4) from g498,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨e (.n 1012), outCell_sound _ σ KTs 115 1012 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1012) = qv inp (.HB 3 4) from g499,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨e (.n 1011), outCell_sound _ σ KTs 116 1011 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1011) = qv inp (.HB 3 5) from g500,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨e (.n 1010), outCell_sound _ σ KTs 117 1010 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1010) = qv inp (.HB 3 5) from g501,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨e (.n 1009), outCell_sound _ σ KTs 118 1009 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1009) = qv inp (.HB 3 5) from g502,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨e (.n 1008), outCell_sound _ σ KTs 119 1008 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1008) = qv inp (.HB 3 5) from g503,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨e (.n 1007), outCell_sound _ σ KTs 120 1007 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1007) = qv inp (.HB 3 6) from g504,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨e (.n 1006), outCell_sound _ σ KTs 121 1006 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1006) = qv inp (.HB 3 6) from g505,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨e (.n 1005), outCell_sound _ σ KTs 122 1005 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1005) = qv inp (.HB 3 6) from g506,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨e (.n 1004), outCell_sound _ σ KTs 123 1004 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1004) = qv inp (.HB 3 6) from g507,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨e (.n 1003), outCell_sound _ σ KTs 124 1003 0 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1003) = qv inp (.HB 3 7) from g508,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨e (.n 1002), outCell_sound _ σ KTs 125 1002 1 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1002) = qv inp (.HB 3 7) from g509,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨e (.n 1001), outCell_sound _ σ KTs 126 1001 2 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1001) = qv inp (.HB 3 7) from g510,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨e (.n 1000), outCell_sound _ σ KTs 127 1000 3 (w4cell_KTs _ _ _ (by decide)),
      by rw [show e (.n 1000) = qv inp (.HB 3 7) from g511,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 4, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega

/-- The write log of a tail ending in `KTEs` holds the 4 digests, from the invariant at `L204`. -/
theorem w4outOk_KTEs (inp : Nat → Byte) (e : Key → W32) (σ : Nat → Int) (hI : InvC inp e L204) :
    OutOk inp (σ 1) 4 (mapState e σ KTEs).mem := by
  have hF := hI
  have g0 := hF.1; have hF := hF.2
  have g1 := hF.1; have hF := hF.2
  have g2 := hF.1; have hF := hF.2
  have g3 := hF.1; have hF := hF.2
  have g4 := hF.1; have hF := hF.2
  have g5 := hF.1; have hF := hF.2
  have g6 := hF.1; have hF := hF.2
  have g7 := hF.1; have hF := hF.2
  have g8 := hF.1; have hF := hF.2
  have g9 := hF.1; have hF := hF.2
  have g10 := hF.1; have hF := hF.2
  have g11 := hF.1; have hF := hF.2
  have g12 := hF.1; have hF := hF.2
  have g13 := hF.1; have hF := hF.2
  have g14 := hF.1; have hF := hF.2
  have g15 := hF.1; have hF := hF.2
  have g16 := hF.1; have hF := hF.2
  have g17 := hF.1; have hF := hF.2
  have g18 := hF.1; have hF := hF.2
  have g19 := hF.1; have hF := hF.2
  have g20 := hF.1; have hF := hF.2
  have g21 := hF.1; have hF := hF.2
  have g22 := hF.1; have hF := hF.2
  have g23 := hF.1; have hF := hF.2
  have g24 := hF.1; have hF := hF.2
  have g25 := hF.1; have hF := hF.2
  have g26 := hF.1; have hF := hF.2
  have g27 := hF.1; have hF := hF.2
  have g28 := hF.1; have hF := hF.2
  have g29 := hF.1; have hF := hF.2
  have g30 := hF.1; have hF := hF.2
  have g31 := hF.1; have hF := hF.2
  have g32 := hF.1; have hF := hF.2
  have g33 := hF.1; have hF := hF.2
  have g34 := hF.1; have hF := hF.2
  have g35 := hF.1; have hF := hF.2
  have g36 := hF.1; have hF := hF.2
  have g37 := hF.1; have hF := hF.2
  have g38 := hF.1; have hF := hF.2
  have g39 := hF.1; have hF := hF.2
  have g40 := hF.1; have hF := hF.2
  have g41 := hF.1; have hF := hF.2
  have g42 := hF.1; have hF := hF.2
  have g43 := hF.1; have hF := hF.2
  have g44 := hF.1; have hF := hF.2
  have g45 := hF.1; have hF := hF.2
  have g46 := hF.1; have hF := hF.2
  have g47 := hF.1; have hF := hF.2
  have g48 := hF.1; have hF := hF.2
  have g49 := hF.1; have hF := hF.2
  have g50 := hF.1; have hF := hF.2
  have g51 := hF.1; have hF := hF.2
  have g52 := hF.1; have hF := hF.2
  have g53 := hF.1; have hF := hF.2
  have g54 := hF.1; have hF := hF.2
  have g55 := hF.1; have hF := hF.2
  have g56 := hF.1; have hF := hF.2
  have g57 := hF.1; have hF := hF.2
  have g58 := hF.1; have hF := hF.2
  have g59 := hF.1; have hF := hF.2
  have g60 := hF.1; have hF := hF.2
  have g61 := hF.1; have hF := hF.2
  have g62 := hF.1; have hF := hF.2
  have g63 := hF.1; have hF := hF.2
  have g64 := hF.1; have hF := hF.2
  have g65 := hF.1; have hF := hF.2
  have g66 := hF.1; have hF := hF.2
  have g67 := hF.1; have hF := hF.2
  have g68 := hF.1; have hF := hF.2
  have g69 := hF.1; have hF := hF.2
  have g70 := hF.1; have hF := hF.2
  have g71 := hF.1; have hF := hF.2
  have g72 := hF.1; have hF := hF.2
  have g73 := hF.1; have hF := hF.2
  have g74 := hF.1; have hF := hF.2
  have g75 := hF.1; have hF := hF.2
  have g76 := hF.1; have hF := hF.2
  have g77 := hF.1; have hF := hF.2
  have g78 := hF.1; have hF := hF.2
  have g79 := hF.1; have hF := hF.2
  have g80 := hF.1; have hF := hF.2
  have g81 := hF.1; have hF := hF.2
  have g82 := hF.1; have hF := hF.2
  have g83 := hF.1; have hF := hF.2
  have g84 := hF.1; have hF := hF.2
  have g85 := hF.1; have hF := hF.2
  have g86 := hF.1; have hF := hF.2
  have g87 := hF.1; have hF := hF.2
  have g88 := hF.1; have hF := hF.2
  have g89 := hF.1; have hF := hF.2
  have g90 := hF.1; have hF := hF.2
  have g91 := hF.1; have hF := hF.2
  have g92 := hF.1; have hF := hF.2
  have g93 := hF.1; have hF := hF.2
  have g94 := hF.1; have hF := hF.2
  have g95 := hF.1; have hF := hF.2
  have g96 := hF.1; have hF := hF.2
  have g97 := hF.1; have hF := hF.2
  have g98 := hF.1; have hF := hF.2
  have g99 := hF.1; have hF := hF.2
  have g100 := hF.1; have hF := hF.2
  have g101 := hF.1; have hF := hF.2
  have g102 := hF.1; have hF := hF.2
  have g103 := hF.1; have hF := hF.2
  have g104 := hF.1; have hF := hF.2
  have g105 := hF.1; have hF := hF.2
  have g106 := hF.1; have hF := hF.2
  have g107 := hF.1; have hF := hF.2
  have g108 := hF.1; have hF := hF.2
  have g109 := hF.1; have hF := hF.2
  have g110 := hF.1; have hF := hF.2
  have g111 := hF.1; have hF := hF.2
  have g112 := hF.1; have hF := hF.2
  have g113 := hF.1; have hF := hF.2
  have g114 := hF.1; have hF := hF.2
  have g115 := hF.1; have hF := hF.2
  have g116 := hF.1; have hF := hF.2
  have g117 := hF.1; have hF := hF.2
  have g118 := hF.1; have hF := hF.2
  have g119 := hF.1; have hF := hF.2
  have g120 := hF.1; have hF := hF.2
  have g121 := hF.1; have hF := hF.2
  have g122 := hF.1; have hF := hF.2
  have g123 := hF.1; have hF := hF.2
  have g124 := hF.1; have hF := hF.2
  have g125 := hF.1; have hF := hF.2
  have g126 := hF.1; have hF := hF.2
  have g127 := hF.1; have hF := hF.2
  have g128 := hF.1; have hF := hF.2
  have g129 := hF.1; have hF := hF.2
  have g130 := hF.1; have hF := hF.2
  have g131 := hF.1; have hF := hF.2
  have g132 := hF.1; have hF := hF.2
  have g133 := hF.1; have hF := hF.2
  have g134 := hF.1; have hF := hF.2
  have g135 := hF.1; have hF := hF.2
  have g136 := hF.1; have hF := hF.2
  have g137 := hF.1; have hF := hF.2
  have g138 := hF.1; have hF := hF.2
  have g139 := hF.1; have hF := hF.2
  have g140 := hF.1; have hF := hF.2
  have g141 := hF.1; have hF := hF.2
  have g142 := hF.1; have hF := hF.2
  have g143 := hF.1; have hF := hF.2
  have g144 := hF.1; have hF := hF.2
  have g145 := hF.1; have hF := hF.2
  have g146 := hF.1; have hF := hF.2
  have g147 := hF.1; have hF := hF.2
  have g148 := hF.1; have hF := hF.2
  have g149 := hF.1; have hF := hF.2
  have g150 := hF.1; have hF := hF.2
  have g151 := hF.1; have hF := hF.2
  have g152 := hF.1; have hF := hF.2
  have g153 := hF.1; have hF := hF.2
  have g154 := hF.1; have hF := hF.2
  have g155 := hF.1; have hF := hF.2
  have g156 := hF.1; have hF := hF.2
  have g157 := hF.1; have hF := hF.2
  have g158 := hF.1; have hF := hF.2
  have g159 := hF.1; have hF := hF.2
  have g160 := hF.1; have hF := hF.2
  have g161 := hF.1; have hF := hF.2
  have g162 := hF.1; have hF := hF.2
  have g163 := hF.1; have hF := hF.2
  have g164 := hF.1; have hF := hF.2
  have g165 := hF.1; have hF := hF.2
  have g166 := hF.1; have hF := hF.2
  have g167 := hF.1; have hF := hF.2
  have g168 := hF.1; have hF := hF.2
  have g169 := hF.1; have hF := hF.2
  have g170 := hF.1; have hF := hF.2
  have g171 := hF.1; have hF := hF.2
  have g172 := hF.1; have hF := hF.2
  have g173 := hF.1; have hF := hF.2
  have g174 := hF.1; have hF := hF.2
  have g175 := hF.1; have hF := hF.2
  have g176 := hF.1; have hF := hF.2
  have g177 := hF.1; have hF := hF.2
  have g178 := hF.1; have hF := hF.2
  have g179 := hF.1; have hF := hF.2
  have g180 := hF.1; have hF := hF.2
  have g181 := hF.1; have hF := hF.2
  have g182 := hF.1; have hF := hF.2
  have g183 := hF.1; have hF := hF.2
  have g184 := hF.1; have hF := hF.2
  have g185 := hF.1; have hF := hF.2
  have g186 := hF.1; have hF := hF.2
  have g187 := hF.1; have hF := hF.2
  have g188 := hF.1; have hF := hF.2
  have g189 := hF.1; have hF := hF.2
  have g190 := hF.1; have hF := hF.2
  have g191 := hF.1; have hF := hF.2
  have g192 := hF.1; have hF := hF.2
  have g193 := hF.1; have hF := hF.2
  have g194 := hF.1; have hF := hF.2
  have g195 := hF.1; have hF := hF.2
  have g196 := hF.1; have hF := hF.2
  have g197 := hF.1; have hF := hF.2
  have g198 := hF.1; have hF := hF.2
  have g199 := hF.1; have hF := hF.2
  have g200 := hF.1; have hF := hF.2
  have g201 := hF.1; have hF := hF.2
  have g202 := hF.1; have hF := hF.2
  have g203 := hF.1; have hF := hF.2
  have g204 := hF.1; have hF := hF.2
  have g205 := hF.1; have hF := hF.2
  have g206 := hF.1; have hF := hF.2
  have g207 := hF.1; have hF := hF.2
  have g208 := hF.1; have hF := hF.2
  have g209 := hF.1; have hF := hF.2
  have g210 := hF.1; have hF := hF.2
  have g211 := hF.1; have hF := hF.2
  have g212 := hF.1; have hF := hF.2
  have g213 := hF.1; have hF := hF.2
  have g214 := hF.1; have hF := hF.2
  have g215 := hF.1; have hF := hF.2
  have g216 := hF.1; have hF := hF.2
  have g217 := hF.1; have hF := hF.2
  have g218 := hF.1; have hF := hF.2
  have g219 := hF.1; have hF := hF.2
  have g220 := hF.1; have hF := hF.2
  have g221 := hF.1; have hF := hF.2
  have g222 := hF.1; have hF := hF.2
  have g223 := hF.1; have hF := hF.2
  have g224 := hF.1; have hF := hF.2
  have g225 := hF.1; have hF := hF.2
  have g226 := hF.1; have hF := hF.2
  have g227 := hF.1; have hF := hF.2
  have g228 := hF.1; have hF := hF.2
  have g229 := hF.1; have hF := hF.2
  have g230 := hF.1; have hF := hF.2
  have g231 := hF.1; have hF := hF.2
  have g232 := hF.1; have hF := hF.2
  have g233 := hF.1; have hF := hF.2
  have g234 := hF.1; have hF := hF.2
  have g235 := hF.1; have hF := hF.2
  have g236 := hF.1; have hF := hF.2
  have g237 := hF.1; have hF := hF.2
  have g238 := hF.1; have hF := hF.2
  have g239 := hF.1; have hF := hF.2
  have g240 := hF.1; have hF := hF.2
  have g241 := hF.1; have hF := hF.2
  have g242 := hF.1; have hF := hF.2
  have g243 := hF.1; have hF := hF.2
  have g244 := hF.1; have hF := hF.2
  have g245 := hF.1; have hF := hF.2
  have g246 := hF.1; have hF := hF.2
  have g247 := hF.1; have hF := hF.2
  have g248 := hF.1; have hF := hF.2
  have g249 := hF.1; have hF := hF.2
  have g250 := hF.1; have hF := hF.2
  have g251 := hF.1; have hF := hF.2
  have g252 := hF.1; have hF := hF.2
  have g253 := hF.1; have hF := hF.2
  have g254 := hF.1; have hF := hF.2
  have g255 := hF.1; have hF := hF.2
  have g256 := hF.1; have hF := hF.2
  have g257 := hF.1; have hF := hF.2
  have g258 := hF.1; have hF := hF.2
  have g259 := hF.1; have hF := hF.2
  have g260 := hF.1; have hF := hF.2
  have g261 := hF.1; have hF := hF.2
  have g262 := hF.1; have hF := hF.2
  have g263 := hF.1; have hF := hF.2
  have g264 := hF.1; have hF := hF.2
  have g265 := hF.1; have hF := hF.2
  have g266 := hF.1; have hF := hF.2
  have g267 := hF.1; have hF := hF.2
  have g268 := hF.1; have hF := hF.2
  have g269 := hF.1; have hF := hF.2
  have g270 := hF.1; have hF := hF.2
  have g271 := hF.1; have hF := hF.2
  have g272 := hF.1; have hF := hF.2
  have g273 := hF.1; have hF := hF.2
  have g274 := hF.1; have hF := hF.2
  have g275 := hF.1; have hF := hF.2
  have g276 := hF.1; have hF := hF.2
  have g277 := hF.1; have hF := hF.2
  have g278 := hF.1; have hF := hF.2
  have g279 := hF.1; have hF := hF.2
  have g280 := hF.1; have hF := hF.2
  have g281 := hF.1; have hF := hF.2
  have g282 := hF.1; have hF := hF.2
  have g283 := hF.1; have hF := hF.2
  have g284 := hF.1; have hF := hF.2
  have g285 := hF.1; have hF := hF.2
  have g286 := hF.1; have hF := hF.2
  have g287 := hF.1; have hF := hF.2
  have g288 := hF.1; have hF := hF.2
  have g289 := hF.1; have hF := hF.2
  have g290 := hF.1; have hF := hF.2
  have g291 := hF.1; have hF := hF.2
  have g292 := hF.1; have hF := hF.2
  have g293 := hF.1; have hF := hF.2
  have g294 := hF.1; have hF := hF.2
  have g295 := hF.1; have hF := hF.2
  have g296 := hF.1; have hF := hF.2
  have g297 := hF.1; have hF := hF.2
  have g298 := hF.1; have hF := hF.2
  have g299 := hF.1; have hF := hF.2
  have g300 := hF.1; have hF := hF.2
  have g301 := hF.1; have hF := hF.2
  have g302 := hF.1; have hF := hF.2
  have g303 := hF.1; have hF := hF.2
  have g304 := hF.1; have hF := hF.2
  have g305 := hF.1; have hF := hF.2
  have g306 := hF.1; have hF := hF.2
  have g307 := hF.1; have hF := hF.2
  have g308 := hF.1; have hF := hF.2
  have g309 := hF.1; have hF := hF.2
  have g310 := hF.1; have hF := hF.2
  have g311 := hF.1; have hF := hF.2
  have g312 := hF.1; have hF := hF.2
  have g313 := hF.1; have hF := hF.2
  have g314 := hF.1; have hF := hF.2
  have g315 := hF.1; have hF := hF.2
  have g316 := hF.1; have hF := hF.2
  have g317 := hF.1; have hF := hF.2
  have g318 := hF.1; have hF := hF.2
  have g319 := hF.1; have hF := hF.2
  have g320 := hF.1; have hF := hF.2
  have g321 := hF.1; have hF := hF.2
  have g322 := hF.1; have hF := hF.2
  have g323 := hF.1; have hF := hF.2
  have g324 := hF.1; have hF := hF.2
  have g325 := hF.1; have hF := hF.2
  have g326 := hF.1; have hF := hF.2
  have g327 := hF.1; have hF := hF.2
  have g328 := hF.1; have hF := hF.2
  have g329 := hF.1; have hF := hF.2
  have g330 := hF.1; have hF := hF.2
  have g331 := hF.1; have hF := hF.2
  have g332 := hF.1; have hF := hF.2
  have g333 := hF.1; have hF := hF.2
  have g334 := hF.1; have hF := hF.2
  have g335 := hF.1; have hF := hF.2
  have g336 := hF.1; have hF := hF.2
  have g337 := hF.1; have hF := hF.2
  have g338 := hF.1; have hF := hF.2
  have g339 := hF.1; have hF := hF.2
  have g340 := hF.1; have hF := hF.2
  have g341 := hF.1; have hF := hF.2
  have g342 := hF.1; have hF := hF.2
  have g343 := hF.1; have hF := hF.2
  have g344 := hF.1; have hF := hF.2
  have g345 := hF.1; have hF := hF.2
  have g346 := hF.1; have hF := hF.2
  have g347 := hF.1; have hF := hF.2
  have g348 := hF.1; have hF := hF.2
  have g349 := hF.1; have hF := hF.2
  have g350 := hF.1; have hF := hF.2
  have g351 := hF.1; have hF := hF.2
  have g352 := hF.1; have hF := hF.2
  have g353 := hF.1; have hF := hF.2
  have g354 := hF.1; have hF := hF.2
  have g355 := hF.1; have hF := hF.2
  have g356 := hF.1; have hF := hF.2
  have g357 := hF.1; have hF := hF.2
  have g358 := hF.1; have hF := hF.2
  have g359 := hF.1; have hF := hF.2
  have g360 := hF.1; have hF := hF.2
  have g361 := hF.1; have hF := hF.2
  have g362 := hF.1; have hF := hF.2
  have g363 := hF.1; have hF := hF.2
  have g364 := hF.1; have hF := hF.2
  have g365 := hF.1; have hF := hF.2
  have g366 := hF.1; have hF := hF.2
  have g367 := hF.1; have hF := hF.2
  have g368 := hF.1; have hF := hF.2
  have g369 := hF.1; have hF := hF.2
  have g370 := hF.1; have hF := hF.2
  have g371 := hF.1; have hF := hF.2
  have g372 := hF.1; have hF := hF.2
  have g373 := hF.1; have hF := hF.2
  have g374 := hF.1; have hF := hF.2
  have g375 := hF.1; have hF := hF.2
  have g376 := hF.1; have hF := hF.2
  have g377 := hF.1; have hF := hF.2
  have g378 := hF.1; have hF := hF.2
  have g379 := hF.1; have hF := hF.2
  have g380 := hF.1; have hF := hF.2
  have g381 := hF.1; have hF := hF.2
  have g382 := hF.1; have hF := hF.2
  have g383 := hF.1; have hF := hF.2
  have g384 := hF.1; have hF := hF.2
  have g385 := hF.1; have hF := hF.2
  have g386 := hF.1; have hF := hF.2
  have g387 := hF.1; have hF := hF.2
  have g388 := hF.1; have hF := hF.2
  have g389 := hF.1; have hF := hF.2
  have g390 := hF.1; have hF := hF.2
  have g391 := hF.1; have hF := hF.2
  have g392 := hF.1; have hF := hF.2
  have g393 := hF.1; have hF := hF.2
  have g394 := hF.1; have hF := hF.2
  have g395 := hF.1; have hF := hF.2
  have g396 := hF.1; have hF := hF.2
  have g397 := hF.1; have hF := hF.2
  have g398 := hF.1; have hF := hF.2
  have g399 := hF.1; have hF := hF.2
  have g400 := hF.1; have hF := hF.2
  have g401 := hF.1; have hF := hF.2
  have g402 := hF.1; have hF := hF.2
  have g403 := hF.1; have hF := hF.2
  have g404 := hF.1; have hF := hF.2
  have g405 := hF.1; have hF := hF.2
  have g406 := hF.1; have hF := hF.2
  have g407 := hF.1; have hF := hF.2
  have g408 := hF.1; have hF := hF.2
  have g409 := hF.1; have hF := hF.2
  have g410 := hF.1; have hF := hF.2
  have g411 := hF.1; have hF := hF.2
  have g412 := hF.1; have hF := hF.2
  have g413 := hF.1; have hF := hF.2
  have g414 := hF.1; have hF := hF.2
  have g415 := hF.1; have hF := hF.2
  have g416 := hF.1; have hF := hF.2
  have g417 := hF.1; have hF := hF.2
  have g418 := hF.1; have hF := hF.2
  have g419 := hF.1; have hF := hF.2
  have g420 := hF.1; have hF := hF.2
  have g421 := hF.1; have hF := hF.2
  have g422 := hF.1; have hF := hF.2
  have g423 := hF.1; have hF := hF.2
  have g424 := hF.1; have hF := hF.2
  have g425 := hF.1; have hF := hF.2
  have g426 := hF.1; have hF := hF.2
  have g427 := hF.1; have hF := hF.2
  have g428 := hF.1; have hF := hF.2
  have g429 := hF.1; have hF := hF.2
  have g430 := hF.1; have hF := hF.2
  have g431 := hF.1; have hF := hF.2
  have g432 := hF.1; have hF := hF.2
  have g433 := hF.1; have hF := hF.2
  have g434 := hF.1; have hF := hF.2
  have g435 := hF.1; have hF := hF.2
  have g436 := hF.1; have hF := hF.2
  have g437 := hF.1; have hF := hF.2
  have g438 := hF.1; have hF := hF.2
  have g439 := hF.1; have hF := hF.2
  have g440 := hF.1; have hF := hF.2
  have g441 := hF.1; have hF := hF.2
  have g442 := hF.1; have hF := hF.2
  have g443 := hF.1; have hF := hF.2
  have g444 := hF.1; have hF := hF.2
  have g445 := hF.1; have hF := hF.2
  have g446 := hF.1; have hF := hF.2
  have g447 := hF.1; have hF := hF.2
  have g448 := hF.1; have hF := hF.2
  have g449 := hF.1; have hF := hF.2
  have g450 := hF.1; have hF := hF.2
  have g451 := hF.1; have hF := hF.2
  have g452 := hF.1; have hF := hF.2
  have g453 := hF.1; have hF := hF.2
  have g454 := hF.1; have hF := hF.2
  have g455 := hF.1; have hF := hF.2
  have g456 := hF.1; have hF := hF.2
  have g457 := hF.1; have hF := hF.2
  have g458 := hF.1; have hF := hF.2
  have g459 := hF.1; have hF := hF.2
  have g460 := hF.1; have hF := hF.2
  have g461 := hF.1; have hF := hF.2
  have g462 := hF.1; have hF := hF.2
  have g463 := hF.1; have hF := hF.2
  have g464 := hF.1; have hF := hF.2
  have g465 := hF.1; have hF := hF.2
  have g466 := hF.1; have hF := hF.2
  have g467 := hF.1; have hF := hF.2
  have g468 := hF.1; have hF := hF.2
  have g469 := hF.1; have hF := hF.2
  have g470 := hF.1; have hF := hF.2
  have g471 := hF.1; have hF := hF.2
  have g472 := hF.1; have hF := hF.2
  have g473 := hF.1; have hF := hF.2
  have g474 := hF.1; have hF := hF.2
  have g475 := hF.1; have hF := hF.2
  have g476 := hF.1; have hF := hF.2
  have g477 := hF.1; have hF := hF.2
  have g478 := hF.1; have hF := hF.2
  have g479 := hF.1; have hF := hF.2
  have g480 := hF.1; have hF := hF.2
  have g481 := hF.1; have hF := hF.2
  have g482 := hF.1; have hF := hF.2
  have g483 := hF.1; have hF := hF.2
  have g484 := hF.1; have hF := hF.2
  have g485 := hF.1; have hF := hF.2
  have g486 := hF.1; have hF := hF.2
  have g487 := hF.1; have hF := hF.2
  have g488 := hF.1; have hF := hF.2
  have g489 := hF.1; have hF := hF.2
  have g490 := hF.1; have hF := hF.2
  have g491 := hF.1; have hF := hF.2
  have g492 := hF.1; have hF := hF.2
  have g493 := hF.1; have hF := hF.2
  have g494 := hF.1; have hF := hF.2
  have g495 := hF.1; have hF := hF.2
  have g496 := hF.1; have hF := hF.2
  have g497 := hF.1; have hF := hF.2
  have g498 := hF.1; have hF := hF.2
  have g499 := hF.1; have hF := hF.2
  have g500 := hF.1; have hF := hF.2
  have g501 := hF.1; have hF := hF.2
  have g502 := hF.1; have hF := hF.2
  have g503 := hF.1; have hF := hF.2
  have g504 := hF.1; have hF := hF.2
  have g505 := hF.1; have hF := hF.2
  have g506 := hF.1; have hF := hF.2
  have g507 := hF.1; have hF := hF.2
  have g508 := hF.1; have hF := hF.2
  have g509 := hF.1; have hF := hF.2
  have g510 := hF.1; have hF := hF.2
  have g511 := hF.1; have hF := hF.2
  have g512 := hF.1; have hF := hF.2
  have g513 := hF.1; have hF := hF.2
  have g514 := hF.1; have hF := hF.2
  have g515 := hF.1; have hF := hF.2
  have g516 := hF.1; have hF := hF.2
  have g517 := hF.1; have hF := hF.2
  have g518 := hF.1; have hF := hF.2
  have g519 := hF.1; have hF := hF.2
  have g520 := hF.1; have hF := hF.2
  have g521 := hF.1; have hF := hF.2
  have g522 := hF.1; have hF := hF.2
  have g523 := hF.1; have hF := hF.2
  have g524 := hF.1; have hF := hF.2
  have g525 := hF.1; have hF := hF.2
  have g526 := hF.1; have hF := hF.2
  have g527 := hF.1; have hF := hF.2
  have g528 := hF.1; have hF := hF.2
  have g529 := hF.1; have hF := hF.2
  have g530 := hF.1; have hF := hF.2
  have g531 := hF.1; have hF := hF.2
  have g532 := hF.1; have hF := hF.2
  have g533 := hF.1; have hF := hF.2
  have g534 := hF.1; have hF := hF.2
  have g535 := hF.1; have hF := hF.2
  intro n i b hn hi hb
  match n, i, b, hn, hi, hb with
  | 0, 0, 0, _, _, _ => exact ⟨e (.n 1127), outCell_sound _ σ KTEs 0 1127 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1127) = qv inp (.HB 0 0) from g384,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 0 0 (by decide) (by decide)]; rfl⟩
  | 0, 0, 1, _, _, _ => exact ⟨e (.n 1126), outCell_sound _ σ KTEs 1 1126 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1126) = qv inp (.HB 0 0) from g385,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 0 1 (by decide) (by decide)]; rfl⟩
  | 0, 0, 2, _, _, _ => exact ⟨e (.n 1125), outCell_sound _ σ KTEs 2 1125 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1125) = qv inp (.HB 0 0) from g386,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 0 2 (by decide) (by decide)]; rfl⟩
  | 0, 0, 3, _, _, _ => exact ⟨e (.n 1124), outCell_sound _ σ KTEs 3 1124 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1124) = qv inp (.HB 0 0) from g387,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 0 3 (by decide) (by decide)]; rfl⟩
  | 0, 1, 0, _, _, _ => exact ⟨e (.n 1123), outCell_sound _ σ KTEs 4 1123 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1123) = qv inp (.HB 0 1) from g388,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 1 0 (by decide) (by decide)]; rfl⟩
  | 0, 1, 1, _, _, _ => exact ⟨e (.n 1122), outCell_sound _ σ KTEs 5 1122 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1122) = qv inp (.HB 0 1) from g389,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 1 1 (by decide) (by decide)]; rfl⟩
  | 0, 1, 2, _, _, _ => exact ⟨e (.n 1121), outCell_sound _ σ KTEs 6 1121 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1121) = qv inp (.HB 0 1) from g390,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 1 2 (by decide) (by decide)]; rfl⟩
  | 0, 1, 3, _, _, _ => exact ⟨e (.n 1120), outCell_sound _ σ KTEs 7 1120 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1120) = qv inp (.HB 0 1) from g391,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 1 3 (by decide) (by decide)]; rfl⟩
  | 0, 2, 0, _, _, _ => exact ⟨e (.n 1119), outCell_sound _ σ KTEs 8 1119 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1119) = qv inp (.HB 0 2) from g392,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 2 0 (by decide) (by decide)]; rfl⟩
  | 0, 2, 1, _, _, _ => exact ⟨e (.n 1118), outCell_sound _ σ KTEs 9 1118 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1118) = qv inp (.HB 0 2) from g393,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 2 1 (by decide) (by decide)]; rfl⟩
  | 0, 2, 2, _, _, _ => exact ⟨e (.n 1117), outCell_sound _ σ KTEs 10 1117 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1117) = qv inp (.HB 0 2) from g394,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 2 2 (by decide) (by decide)]; rfl⟩
  | 0, 2, 3, _, _, _ => exact ⟨e (.n 1116), outCell_sound _ σ KTEs 11 1116 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1116) = qv inp (.HB 0 2) from g395,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 2 3 (by decide) (by decide)]; rfl⟩
  | 0, 3, 0, _, _, _ => exact ⟨e (.n 1115), outCell_sound _ σ KTEs 12 1115 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1115) = qv inp (.HB 0 3) from g396,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 3 0 (by decide) (by decide)]; rfl⟩
  | 0, 3, 1, _, _, _ => exact ⟨e (.n 1114), outCell_sound _ σ KTEs 13 1114 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1114) = qv inp (.HB 0 3) from g397,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 3 1 (by decide) (by decide)]; rfl⟩
  | 0, 3, 2, _, _, _ => exact ⟨e (.n 1113), outCell_sound _ σ KTEs 14 1113 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1113) = qv inp (.HB 0 3) from g398,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 3 2 (by decide) (by decide)]; rfl⟩
  | 0, 3, 3, _, _, _ => exact ⟨e (.n 1112), outCell_sound _ σ KTEs 15 1112 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1112) = qv inp (.HB 0 3) from g399,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 3 3 (by decide) (by decide)]; rfl⟩
  | 0, 4, 0, _, _, _ => exact ⟨e (.n 1111), outCell_sound _ σ KTEs 16 1111 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1111) = qv inp (.HB 0 4) from g400,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 4 0 (by decide) (by decide)]; rfl⟩
  | 0, 4, 1, _, _, _ => exact ⟨e (.n 1110), outCell_sound _ σ KTEs 17 1110 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1110) = qv inp (.HB 0 4) from g401,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 4 1 (by decide) (by decide)]; rfl⟩
  | 0, 4, 2, _, _, _ => exact ⟨e (.n 1109), outCell_sound _ σ KTEs 18 1109 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1109) = qv inp (.HB 0 4) from g402,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 4 2 (by decide) (by decide)]; rfl⟩
  | 0, 4, 3, _, _, _ => exact ⟨e (.n 1108), outCell_sound _ σ KTEs 19 1108 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1108) = qv inp (.HB 0 4) from g403,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 4 3 (by decide) (by decide)]; rfl⟩
  | 0, 5, 0, _, _, _ => exact ⟨e (.n 1107), outCell_sound _ σ KTEs 20 1107 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1107) = qv inp (.HB 0 5) from g404,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 5 0 (by decide) (by decide)]; rfl⟩
  | 0, 5, 1, _, _, _ => exact ⟨e (.n 1106), outCell_sound _ σ KTEs 21 1106 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1106) = qv inp (.HB 0 5) from g405,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 5 1 (by decide) (by decide)]; rfl⟩
  | 0, 5, 2, _, _, _ => exact ⟨e (.n 1105), outCell_sound _ σ KTEs 22 1105 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1105) = qv inp (.HB 0 5) from g406,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 5 2 (by decide) (by decide)]; rfl⟩
  | 0, 5, 3, _, _, _ => exact ⟨e (.n 1104), outCell_sound _ σ KTEs 23 1104 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1104) = qv inp (.HB 0 5) from g407,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 5 3 (by decide) (by decide)]; rfl⟩
  | 0, 6, 0, _, _, _ => exact ⟨e (.n 1103), outCell_sound _ σ KTEs 24 1103 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1103) = qv inp (.HB 0 6) from g408,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 6 0 (by decide) (by decide)]; rfl⟩
  | 0, 6, 1, _, _, _ => exact ⟨e (.n 1102), outCell_sound _ σ KTEs 25 1102 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1102) = qv inp (.HB 0 6) from g409,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 6 1 (by decide) (by decide)]; rfl⟩
  | 0, 6, 2, _, _, _ => exact ⟨e (.n 1101), outCell_sound _ σ KTEs 26 1101 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1101) = qv inp (.HB 0 6) from g410,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 6 2 (by decide) (by decide)]; rfl⟩
  | 0, 6, 3, _, _, _ => exact ⟨e (.n 1100), outCell_sound _ σ KTEs 27 1100 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1100) = qv inp (.HB 0 6) from g411,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 6 3 (by decide) (by decide)]; rfl⟩
  | 0, 7, 0, _, _, _ => exact ⟨e (.n 1099), outCell_sound _ σ KTEs 28 1099 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1099) = qv inp (.HB 0 7) from g412,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 0 7 0 (by decide) (by decide)]; rfl⟩
  | 0, 7, 1, _, _, _ => exact ⟨e (.n 1098), outCell_sound _ σ KTEs 29 1098 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1098) = qv inp (.HB 0 7) from g413,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 0 7 1 (by decide) (by decide)]; rfl⟩
  | 0, 7, 2, _, _, _ => exact ⟨e (.n 1097), outCell_sound _ σ KTEs 30 1097 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1097) = qv inp (.HB 0 7) from g414,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 0 7 2 (by decide) (by decide)]; rfl⟩
  | 0, 7, 3, _, _, _ => exact ⟨e (.n 1096), outCell_sound _ σ KTEs 31 1096 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1096) = qv inp (.HB 0 7) from g415,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 0 7 3 (by decide) (by decide)]; rfl⟩
  | 1, 0, 0, _, _, _ => exact ⟨e (.n 1095), outCell_sound _ σ KTEs 32 1095 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1095) = qv inp (.HB 1 0) from g416,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 0 0 (by decide) (by decide)]; rfl⟩
  | 1, 0, 1, _, _, _ => exact ⟨e (.n 1094), outCell_sound _ σ KTEs 33 1094 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1094) = qv inp (.HB 1 0) from g417,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 0 1 (by decide) (by decide)]; rfl⟩
  | 1, 0, 2, _, _, _ => exact ⟨e (.n 1093), outCell_sound _ σ KTEs 34 1093 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1093) = qv inp (.HB 1 0) from g418,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 0 2 (by decide) (by decide)]; rfl⟩
  | 1, 0, 3, _, _, _ => exact ⟨e (.n 1092), outCell_sound _ σ KTEs 35 1092 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1092) = qv inp (.HB 1 0) from g419,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 0 3 (by decide) (by decide)]; rfl⟩
  | 1, 1, 0, _, _, _ => exact ⟨e (.n 1091), outCell_sound _ σ KTEs 36 1091 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1091) = qv inp (.HB 1 1) from g420,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 1 0 (by decide) (by decide)]; rfl⟩
  | 1, 1, 1, _, _, _ => exact ⟨e (.n 1090), outCell_sound _ σ KTEs 37 1090 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1090) = qv inp (.HB 1 1) from g421,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 1 1 (by decide) (by decide)]; rfl⟩
  | 1, 1, 2, _, _, _ => exact ⟨e (.n 1089), outCell_sound _ σ KTEs 38 1089 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1089) = qv inp (.HB 1 1) from g422,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 1 2 (by decide) (by decide)]; rfl⟩
  | 1, 1, 3, _, _, _ => exact ⟨e (.n 1088), outCell_sound _ σ KTEs 39 1088 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1088) = qv inp (.HB 1 1) from g423,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 1 3 (by decide) (by decide)]; rfl⟩
  | 1, 2, 0, _, _, _ => exact ⟨e (.n 1087), outCell_sound _ σ KTEs 40 1087 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1087) = qv inp (.HB 1 2) from g424,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 2 0 (by decide) (by decide)]; rfl⟩
  | 1, 2, 1, _, _, _ => exact ⟨e (.n 1086), outCell_sound _ σ KTEs 41 1086 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1086) = qv inp (.HB 1 2) from g425,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 2 1 (by decide) (by decide)]; rfl⟩
  | 1, 2, 2, _, _, _ => exact ⟨e (.n 1085), outCell_sound _ σ KTEs 42 1085 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1085) = qv inp (.HB 1 2) from g426,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 2 2 (by decide) (by decide)]; rfl⟩
  | 1, 2, 3, _, _, _ => exact ⟨e (.n 1084), outCell_sound _ σ KTEs 43 1084 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1084) = qv inp (.HB 1 2) from g427,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 2 3 (by decide) (by decide)]; rfl⟩
  | 1, 3, 0, _, _, _ => exact ⟨e (.n 1083), outCell_sound _ σ KTEs 44 1083 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1083) = qv inp (.HB 1 3) from g428,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 3 0 (by decide) (by decide)]; rfl⟩
  | 1, 3, 1, _, _, _ => exact ⟨e (.n 1082), outCell_sound _ σ KTEs 45 1082 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1082) = qv inp (.HB 1 3) from g429,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 3 1 (by decide) (by decide)]; rfl⟩
  | 1, 3, 2, _, _, _ => exact ⟨e (.n 1081), outCell_sound _ σ KTEs 46 1081 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1081) = qv inp (.HB 1 3) from g430,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 3 2 (by decide) (by decide)]; rfl⟩
  | 1, 3, 3, _, _, _ => exact ⟨e (.n 1080), outCell_sound _ σ KTEs 47 1080 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1080) = qv inp (.HB 1 3) from g431,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 3 3 (by decide) (by decide)]; rfl⟩
  | 1, 4, 0, _, _, _ => exact ⟨e (.n 1079), outCell_sound _ σ KTEs 48 1079 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1079) = qv inp (.HB 1 4) from g432,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 4 0 (by decide) (by decide)]; rfl⟩
  | 1, 4, 1, _, _, _ => exact ⟨e (.n 1078), outCell_sound _ σ KTEs 49 1078 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1078) = qv inp (.HB 1 4) from g433,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 4 1 (by decide) (by decide)]; rfl⟩
  | 1, 4, 2, _, _, _ => exact ⟨e (.n 1077), outCell_sound _ σ KTEs 50 1077 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1077) = qv inp (.HB 1 4) from g434,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 4 2 (by decide) (by decide)]; rfl⟩
  | 1, 4, 3, _, _, _ => exact ⟨e (.n 1076), outCell_sound _ σ KTEs 51 1076 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1076) = qv inp (.HB 1 4) from g435,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 4 3 (by decide) (by decide)]; rfl⟩
  | 1, 5, 0, _, _, _ => exact ⟨e (.n 1075), outCell_sound _ σ KTEs 52 1075 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1075) = qv inp (.HB 1 5) from g436,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 5 0 (by decide) (by decide)]; rfl⟩
  | 1, 5, 1, _, _, _ => exact ⟨e (.n 1074), outCell_sound _ σ KTEs 53 1074 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1074) = qv inp (.HB 1 5) from g437,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 5 1 (by decide) (by decide)]; rfl⟩
  | 1, 5, 2, _, _, _ => exact ⟨e (.n 1073), outCell_sound _ σ KTEs 54 1073 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1073) = qv inp (.HB 1 5) from g438,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 5 2 (by decide) (by decide)]; rfl⟩
  | 1, 5, 3, _, _, _ => exact ⟨e (.n 1072), outCell_sound _ σ KTEs 55 1072 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1072) = qv inp (.HB 1 5) from g439,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 5 3 (by decide) (by decide)]; rfl⟩
  | 1, 6, 0, _, _, _ => exact ⟨e (.n 1071), outCell_sound _ σ KTEs 56 1071 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1071) = qv inp (.HB 1 6) from g440,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 6 0 (by decide) (by decide)]; rfl⟩
  | 1, 6, 1, _, _, _ => exact ⟨e (.n 1070), outCell_sound _ σ KTEs 57 1070 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1070) = qv inp (.HB 1 6) from g441,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 6 1 (by decide) (by decide)]; rfl⟩
  | 1, 6, 2, _, _, _ => exact ⟨e (.n 1069), outCell_sound _ σ KTEs 58 1069 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1069) = qv inp (.HB 1 6) from g442,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 6 2 (by decide) (by decide)]; rfl⟩
  | 1, 6, 3, _, _, _ => exact ⟨e (.n 1068), outCell_sound _ σ KTEs 59 1068 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1068) = qv inp (.HB 1 6) from g443,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 6 3 (by decide) (by decide)]; rfl⟩
  | 1, 7, 0, _, _, _ => exact ⟨e (.n 1067), outCell_sound _ σ KTEs 60 1067 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1067) = qv inp (.HB 1 7) from g444,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 1 7 0 (by decide) (by decide)]; rfl⟩
  | 1, 7, 1, _, _, _ => exact ⟨e (.n 1066), outCell_sound _ σ KTEs 61 1066 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1066) = qv inp (.HB 1 7) from g445,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 1 7 1 (by decide) (by decide)]; rfl⟩
  | 1, 7, 2, _, _, _ => exact ⟨e (.n 1065), outCell_sound _ σ KTEs 62 1065 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1065) = qv inp (.HB 1 7) from g446,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 1 7 2 (by decide) (by decide)]; rfl⟩
  | 1, 7, 3, _, _, _ => exact ⟨e (.n 1064), outCell_sound _ σ KTEs 63 1064 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1064) = qv inp (.HB 1 7) from g447,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 1 7 3 (by decide) (by decide)]; rfl⟩
  | 2, 0, 0, _, _, _ => exact ⟨e (.n 1063), outCell_sound _ σ KTEs 64 1063 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1063) = qv inp (.HB 2 0) from g448,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 0 0 (by decide) (by decide)]; rfl⟩
  | 2, 0, 1, _, _, _ => exact ⟨e (.n 1062), outCell_sound _ σ KTEs 65 1062 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1062) = qv inp (.HB 2 0) from g449,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 0 1 (by decide) (by decide)]; rfl⟩
  | 2, 0, 2, _, _, _ => exact ⟨e (.n 1061), outCell_sound _ σ KTEs 66 1061 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1061) = qv inp (.HB 2 0) from g450,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 0 2 (by decide) (by decide)]; rfl⟩
  | 2, 0, 3, _, _, _ => exact ⟨e (.n 1060), outCell_sound _ σ KTEs 67 1060 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1060) = qv inp (.HB 2 0) from g451,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 0 3 (by decide) (by decide)]; rfl⟩
  | 2, 1, 0, _, _, _ => exact ⟨e (.n 1059), outCell_sound _ σ KTEs 68 1059 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1059) = qv inp (.HB 2 1) from g452,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 1 0 (by decide) (by decide)]; rfl⟩
  | 2, 1, 1, _, _, _ => exact ⟨e (.n 1058), outCell_sound _ σ KTEs 69 1058 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1058) = qv inp (.HB 2 1) from g453,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 1 1 (by decide) (by decide)]; rfl⟩
  | 2, 1, 2, _, _, _ => exact ⟨e (.n 1057), outCell_sound _ σ KTEs 70 1057 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1057) = qv inp (.HB 2 1) from g454,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 1 2 (by decide) (by decide)]; rfl⟩
  | 2, 1, 3, _, _, _ => exact ⟨e (.n 1056), outCell_sound _ σ KTEs 71 1056 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1056) = qv inp (.HB 2 1) from g455,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 1 3 (by decide) (by decide)]; rfl⟩
  | 2, 2, 0, _, _, _ => exact ⟨e (.n 1055), outCell_sound _ σ KTEs 72 1055 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1055) = qv inp (.HB 2 2) from g456,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 2 0 (by decide) (by decide)]; rfl⟩
  | 2, 2, 1, _, _, _ => exact ⟨e (.n 1054), outCell_sound _ σ KTEs 73 1054 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1054) = qv inp (.HB 2 2) from g457,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 2 1 (by decide) (by decide)]; rfl⟩
  | 2, 2, 2, _, _, _ => exact ⟨e (.n 1053), outCell_sound _ σ KTEs 74 1053 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1053) = qv inp (.HB 2 2) from g458,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 2 2 (by decide) (by decide)]; rfl⟩
  | 2, 2, 3, _, _, _ => exact ⟨e (.n 1052), outCell_sound _ σ KTEs 75 1052 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1052) = qv inp (.HB 2 2) from g459,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 2 3 (by decide) (by decide)]; rfl⟩
  | 2, 3, 0, _, _, _ => exact ⟨e (.n 1051), outCell_sound _ σ KTEs 76 1051 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1051) = qv inp (.HB 2 3) from g460,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 3 0 (by decide) (by decide)]; rfl⟩
  | 2, 3, 1, _, _, _ => exact ⟨e (.n 1050), outCell_sound _ σ KTEs 77 1050 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1050) = qv inp (.HB 2 3) from g461,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 3 1 (by decide) (by decide)]; rfl⟩
  | 2, 3, 2, _, _, _ => exact ⟨e (.n 1049), outCell_sound _ σ KTEs 78 1049 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1049) = qv inp (.HB 2 3) from g462,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 3 2 (by decide) (by decide)]; rfl⟩
  | 2, 3, 3, _, _, _ => exact ⟨e (.n 1048), outCell_sound _ σ KTEs 79 1048 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1048) = qv inp (.HB 2 3) from g463,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 3 3 (by decide) (by decide)]; rfl⟩
  | 2, 4, 0, _, _, _ => exact ⟨e (.n 1047), outCell_sound _ σ KTEs 80 1047 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1047) = qv inp (.HB 2 4) from g464,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 4 0 (by decide) (by decide)]; rfl⟩
  | 2, 4, 1, _, _, _ => exact ⟨e (.n 1046), outCell_sound _ σ KTEs 81 1046 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1046) = qv inp (.HB 2 4) from g465,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 4 1 (by decide) (by decide)]; rfl⟩
  | 2, 4, 2, _, _, _ => exact ⟨e (.n 1045), outCell_sound _ σ KTEs 82 1045 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1045) = qv inp (.HB 2 4) from g466,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 4 2 (by decide) (by decide)]; rfl⟩
  | 2, 4, 3, _, _, _ => exact ⟨e (.n 1044), outCell_sound _ σ KTEs 83 1044 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1044) = qv inp (.HB 2 4) from g467,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 4 3 (by decide) (by decide)]; rfl⟩
  | 2, 5, 0, _, _, _ => exact ⟨e (.n 1043), outCell_sound _ σ KTEs 84 1043 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1043) = qv inp (.HB 2 5) from g468,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 5 0 (by decide) (by decide)]; rfl⟩
  | 2, 5, 1, _, _, _ => exact ⟨e (.n 1042), outCell_sound _ σ KTEs 85 1042 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1042) = qv inp (.HB 2 5) from g469,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 5 1 (by decide) (by decide)]; rfl⟩
  | 2, 5, 2, _, _, _ => exact ⟨e (.n 1041), outCell_sound _ σ KTEs 86 1041 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1041) = qv inp (.HB 2 5) from g470,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 5 2 (by decide) (by decide)]; rfl⟩
  | 2, 5, 3, _, _, _ => exact ⟨e (.n 1040), outCell_sound _ σ KTEs 87 1040 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1040) = qv inp (.HB 2 5) from g471,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 5 3 (by decide) (by decide)]; rfl⟩
  | 2, 6, 0, _, _, _ => exact ⟨e (.n 1039), outCell_sound _ σ KTEs 88 1039 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1039) = qv inp (.HB 2 6) from g472,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 6 0 (by decide) (by decide)]; rfl⟩
  | 2, 6, 1, _, _, _ => exact ⟨e (.n 1038), outCell_sound _ σ KTEs 89 1038 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1038) = qv inp (.HB 2 6) from g473,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 6 1 (by decide) (by decide)]; rfl⟩
  | 2, 6, 2, _, _, _ => exact ⟨e (.n 1037), outCell_sound _ σ KTEs 90 1037 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1037) = qv inp (.HB 2 6) from g474,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 6 2 (by decide) (by decide)]; rfl⟩
  | 2, 6, 3, _, _, _ => exact ⟨e (.n 1036), outCell_sound _ σ KTEs 91 1036 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1036) = qv inp (.HB 2 6) from g475,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 6 3 (by decide) (by decide)]; rfl⟩
  | 2, 7, 0, _, _, _ => exact ⟨e (.n 1035), outCell_sound _ σ KTEs 92 1035 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1035) = qv inp (.HB 2 7) from g476,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 2 7 0 (by decide) (by decide)]; rfl⟩
  | 2, 7, 1, _, _, _ => exact ⟨e (.n 1034), outCell_sound _ σ KTEs 93 1034 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1034) = qv inp (.HB 2 7) from g477,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 2 7 1 (by decide) (by decide)]; rfl⟩
  | 2, 7, 2, _, _, _ => exact ⟨e (.n 1033), outCell_sound _ σ KTEs 94 1033 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1033) = qv inp (.HB 2 7) from g478,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 2 7 2 (by decide) (by decide)]; rfl⟩
  | 2, 7, 3, _, _, _ => exact ⟨e (.n 1032), outCell_sound _ σ KTEs 95 1032 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1032) = qv inp (.HB 2 7) from g479,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 2 7 3 (by decide) (by decide)]; rfl⟩
  | 3, 0, 0, _, _, _ => exact ⟨e (.n 1031), outCell_sound _ σ KTEs 96 1031 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1031) = qv inp (.HB 3 0) from g480,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 0 0 (by decide) (by decide)]; rfl⟩
  | 3, 0, 1, _, _, _ => exact ⟨e (.n 1030), outCell_sound _ σ KTEs 97 1030 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1030) = qv inp (.HB 3 0) from g481,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 0 1 (by decide) (by decide)]; rfl⟩
  | 3, 0, 2, _, _, _ => exact ⟨e (.n 1029), outCell_sound _ σ KTEs 98 1029 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1029) = qv inp (.HB 3 0) from g482,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 0 2 (by decide) (by decide)]; rfl⟩
  | 3, 0, 3, _, _, _ => exact ⟨e (.n 1028), outCell_sound _ σ KTEs 99 1028 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1028) = qv inp (.HB 3 0) from g483,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 0 3 (by decide) (by decide)]; rfl⟩
  | 3, 1, 0, _, _, _ => exact ⟨e (.n 1027), outCell_sound _ σ KTEs 100 1027 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1027) = qv inp (.HB 3 1) from g484,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 1 0 (by decide) (by decide)]; rfl⟩
  | 3, 1, 1, _, _, _ => exact ⟨e (.n 1026), outCell_sound _ σ KTEs 101 1026 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1026) = qv inp (.HB 3 1) from g485,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 1 1 (by decide) (by decide)]; rfl⟩
  | 3, 1, 2, _, _, _ => exact ⟨e (.n 1025), outCell_sound _ σ KTEs 102 1025 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1025) = qv inp (.HB 3 1) from g486,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 1 2 (by decide) (by decide)]; rfl⟩
  | 3, 1, 3, _, _, _ => exact ⟨e (.n 1024), outCell_sound _ σ KTEs 103 1024 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1024) = qv inp (.HB 3 1) from g487,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 1 3 (by decide) (by decide)]; rfl⟩
  | 3, 2, 0, _, _, _ => exact ⟨e (.n 1023), outCell_sound _ σ KTEs 104 1023 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1023) = qv inp (.HB 3 2) from g488,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 2 0 (by decide) (by decide)]; rfl⟩
  | 3, 2, 1, _, _, _ => exact ⟨e (.n 1022), outCell_sound _ σ KTEs 105 1022 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1022) = qv inp (.HB 3 2) from g489,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 2 1 (by decide) (by decide)]; rfl⟩
  | 3, 2, 2, _, _, _ => exact ⟨e (.n 1021), outCell_sound _ σ KTEs 106 1021 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1021) = qv inp (.HB 3 2) from g490,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 2 2 (by decide) (by decide)]; rfl⟩
  | 3, 2, 3, _, _, _ => exact ⟨e (.n 1020), outCell_sound _ σ KTEs 107 1020 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1020) = qv inp (.HB 3 2) from g491,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 2 3 (by decide) (by decide)]; rfl⟩
  | 3, 3, 0, _, _, _ => exact ⟨e (.n 1019), outCell_sound _ σ KTEs 108 1019 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1019) = qv inp (.HB 3 3) from g492,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 3 0 (by decide) (by decide)]; rfl⟩
  | 3, 3, 1, _, _, _ => exact ⟨e (.n 1018), outCell_sound _ σ KTEs 109 1018 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1018) = qv inp (.HB 3 3) from g493,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 3 1 (by decide) (by decide)]; rfl⟩
  | 3, 3, 2, _, _, _ => exact ⟨e (.n 1017), outCell_sound _ σ KTEs 110 1017 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1017) = qv inp (.HB 3 3) from g494,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 3 2 (by decide) (by decide)]; rfl⟩
  | 3, 3, 3, _, _, _ => exact ⟨e (.n 1016), outCell_sound _ σ KTEs 111 1016 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1016) = qv inp (.HB 3 3) from g495,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 3 3 (by decide) (by decide)]; rfl⟩
  | 3, 4, 0, _, _, _ => exact ⟨e (.n 1015), outCell_sound _ σ KTEs 112 1015 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1015) = qv inp (.HB 3 4) from g496,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 4 0 (by decide) (by decide)]; rfl⟩
  | 3, 4, 1, _, _, _ => exact ⟨e (.n 1014), outCell_sound _ σ KTEs 113 1014 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1014) = qv inp (.HB 3 4) from g497,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 4 1 (by decide) (by decide)]; rfl⟩
  | 3, 4, 2, _, _, _ => exact ⟨e (.n 1013), outCell_sound _ σ KTEs 114 1013 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1013) = qv inp (.HB 3 4) from g498,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 4 2 (by decide) (by decide)]; rfl⟩
  | 3, 4, 3, _, _, _ => exact ⟨e (.n 1012), outCell_sound _ σ KTEs 115 1012 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1012) = qv inp (.HB 3 4) from g499,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 4 3 (by decide) (by decide)]; rfl⟩
  | 3, 5, 0, _, _, _ => exact ⟨e (.n 1011), outCell_sound _ σ KTEs 116 1011 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1011) = qv inp (.HB 3 5) from g500,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 5 0 (by decide) (by decide)]; rfl⟩
  | 3, 5, 1, _, _, _ => exact ⟨e (.n 1010), outCell_sound _ σ KTEs 117 1010 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1010) = qv inp (.HB 3 5) from g501,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 5 1 (by decide) (by decide)]; rfl⟩
  | 3, 5, 2, _, _, _ => exact ⟨e (.n 1009), outCell_sound _ σ KTEs 118 1009 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1009) = qv inp (.HB 3 5) from g502,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 5 2 (by decide) (by decide)]; rfl⟩
  | 3, 5, 3, _, _, _ => exact ⟨e (.n 1008), outCell_sound _ σ KTEs 119 1008 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1008) = qv inp (.HB 3 5) from g503,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 5 3 (by decide) (by decide)]; rfl⟩
  | 3, 6, 0, _, _, _ => exact ⟨e (.n 1007), outCell_sound _ σ KTEs 120 1007 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1007) = qv inp (.HB 3 6) from g504,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 6 0 (by decide) (by decide)]; rfl⟩
  | 3, 6, 1, _, _, _ => exact ⟨e (.n 1006), outCell_sound _ σ KTEs 121 1006 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1006) = qv inp (.HB 3 6) from g505,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 6 1 (by decide) (by decide)]; rfl⟩
  | 3, 6, 2, _, _, _ => exact ⟨e (.n 1005), outCell_sound _ σ KTEs 122 1005 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1005) = qv inp (.HB 3 6) from g506,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 6 2 (by decide) (by decide)]; rfl⟩
  | 3, 6, 3, _, _, _ => exact ⟨e (.n 1004), outCell_sound _ σ KTEs 123 1004 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1004) = qv inp (.HB 3 6) from g507,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 6 3 (by decide) (by decide)]; rfl⟩
  | 3, 7, 0, _, _, _ => exact ⟨e (.n 1003), outCell_sound _ σ KTEs 124 1003 0 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1003) = qv inp (.HB 3 7) from g508,
        qHB, byte_bswap _ 0 (by decide), node_byte inp 3 7 0 (by decide) (by decide)]; rfl⟩
  | 3, 7, 1, _, _, _ => exact ⟨e (.n 1002), outCell_sound _ σ KTEs 125 1002 1 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1002) = qv inp (.HB 3 7) from g509,
        qHB, byte_bswap _ 1 (by decide), node_byte inp 3 7 1 (by decide) (by decide)]; rfl⟩
  | 3, 7, 2, _, _, _ => exact ⟨e (.n 1001), outCell_sound _ σ KTEs 126 1001 2 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1001) = qv inp (.HB 3 7) from g510,
        qHB, byte_bswap _ 2 (by decide), node_byte inp 3 7 2 (by decide) (by decide)]; rfl⟩
  | 3, 7, 3, _, _, _ => exact ⟨e (.n 1000), outCell_sound _ σ KTEs 127 1000 3 (w4cell_KTEs _ _ _ (by decide)),
      by rw [show e (.n 1000) = qv inp (.HB 3 7) from g511,
        qHB, byte_bswap _ 3 (by decide), node_byte inp 3 7 3 (by decide) (by decide)]; rfl⟩
  | _ + 4, _, _, hn, _, _ => omega
  | _, _ + 8, _, _, hi, _ => omega
  | _, _, _ + 4, _, _, hb => omega

end Hashtree.Proofs.WinAvxX4WOut
