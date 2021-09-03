include "../../daecore.mc"
include "ad/dualnum.mc"
include "tensor.mc"

let labels =
	[
		"y_1",
		"u_1",
		"t_1",
		"i_1",
		"u_L_1",
		"i_L_1",
		"u_C_1",
		"i_C_1",
		"u_R_1",
		"i_R_1"
	]
let thLabels =
	[]
let th =
	(((tensorOfSeqExn
		tensorCreateDense)
		[0])
		[])
let ivs =
	[(
		(
			2,
			0
		),
		0.
	)]
let probes =
	[(
		0,
		0
	)]
let dae =
	[
		(
			lam xs. lam us. lam ths. lam t.
							let u_R_1 =
								((tensorGetExn
									xs)
									[8])
							in
							let u_L_1 =
									((tensorGetExn
										xs)
										[4])
								in
								let u_1 =
										((tensorGetExn
											xs)
											[1])
									in
									((subn
											(u_R_1
												t))
											((subn
												((subn
													((muln
														(dualnumNum
															(negf 1.)))
														(dualnumNum
															0.)))
													((muln
														(dualnumNum
															1.))
														(u_L_1
															t))))
												((muln
													(dualnumNum
														(negf 1.)))
													(u_1
														t)))),
			[
				(
					8,
					0
				),
				(
					4,
					0
				),
				(
					1,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let u_C_1 =
								((tensorGetExn
									xs)
									[6])
							in
							let u_L_1 =
									((tensorGetExn
										xs)
										[4])
								in
								((subn
										(u_C_1
											t))
										((muln
											(dualnumNum
												1.))
											(u_L_1
												t))),
			[
				(
					6,
					0
				),
				(
					4,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_R_1 =
								((tensorGetExn
									xs)
									[9])
							in
							let u_R_1 =
									((tensorGetExn
										xs)
										[8])
								in
								((subn
										(u_R_1
											t))
										((muln
											(dualnumNum
												2.))
											(i_R_1
												t))),
			[
				(
					9,
					0
				),
				(
					8,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_R_1 =
								((tensorGetExn
									xs)
									[9])
							in
							let i_C_1 =
									((tensorGetExn
										xs)
										[7])
								in
								let i_L_1 =
										((tensorGetExn
											xs)
											[5])
									in
									((subn
											(i_L_1
												t))
											((subn
												((muln
													(dualnumNum
														1.))
													(i_R_1
														t)))
												((muln
													(dualnumNum
														1.))
													(i_C_1
														t)))),
			[
				(
					9,
					0
				),
				(
					7,
					0
				),
				(
					5,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_R_1 =
								((tensorGetExn
									xs)
									[9])
							in
							let y_1 =
									((tensorGetExn
										xs)
										[0])
								in
								((subn
										(y_1
											t))
										((muln
											(dualnumNum
												1.))
											(i_R_1
												t))),
			[
				(
					9,
					0
				),
				(
					0,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_R_1 =
								((tensorGetExn
									xs)
									[9])
							in
							let i_1 =
									((tensorGetExn
										xs)
										[3])
								in
								((subn
										(i_1
											t))
										((muln
											(dualnumNum
												(negf 1.)))
											(i_R_1
												t))),
			[
				(
					9,
					0
				),
				(
					3,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_L_1 =
								((tensorGetExn
									xs)
									[5])
							in
							let u_L_1 =
									((tensorGetExn
										xs)
										[4])
								in
								((subn
										(u_L_1
											t))
										((muln
											(dualnumNum
												4.))
											((der
												i_L_1)
												t))),
			[
				(
					5,
					1
				),
				(
					4,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let i_C_1 =
								((tensorGetExn
									xs)
									[7])
							in
							let u_C_1 =
									((tensorGetExn
										xs)
										[6])
								in
								((subn
										(i_C_1
											t))
										((muln
											(dualnumNum
												3.))
											((der
												u_C_1)
												t))),
			[
				(
					6,
					1
				),
				(
					7,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let t_1 =
								((tensorGetExn
									xs)
									[2])
							in
							let u_1 =
									((tensorGetExn
										xs)
										[1])
								in
								((subn
										(u_1
											t))
										(sinn
											(t_1
												t))),
			[
				(
					2,
					0
				),
				(
					1,
					0
				)
			],
			[]
		),
		(
			lam xs. lam us. lam ths. lam t.
							let t_1 =
								((tensorGetExn
									xs)
									[2])
							in
							((subn
									((der
										t_1)
										t))
									(dualnumNum
										1.)),
			[(
				2,
				1
			)],
			[]
		)
	]

mexpr
dprint (daeInputs dae)
