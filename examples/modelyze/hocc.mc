include "ad/dualnum.mc"
include "tensor.mc"

let labels =
	["x_1"]
let thLabels =
	[
		"c_1",
		"k_1"
	]
let th =
	(((tensorOfSeqExn
		tensorCreateDense)
		[2])
		[
			1.,
			1.
		])
let ivs =
	[(
		(
			0,
			0
		),
		1.
	)]
let probes =
	[(
		0,
		1
	)]
let dae =
	[(
		lam xs. lam us. lam ths. lam t.
						let c_1 =
							((tensorGetExn
								ths)
								[0])
						in
						let k_1 =
								((tensorGetExn
									ths)
									[1])
							in
							let x_1 =
									((tensorGetExn
										xs)
										[0])
								in
								((subn
										(((nder
											2)
											x_1)
											t))
										((addn
											((muln
												(negn
													c_1))
												((der
													x_1)
													t)))
											((muln
												(negn
													k_1))
												(x_1
													t)))),
		[
			(
				0,
				2
			),
			(
				0,
				1
			),
			(
				0,
				0
			)
		],
		[]
	)]
