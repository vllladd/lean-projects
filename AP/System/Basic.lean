import AP.System.Defs

-- theorem mk_system_fn_ap_val_eq {S T : Type} [Inhabited S]
-- {s₀} {f : S → T → Option S} {s t} :
-- (mk_system s₀ f).f s t = f s