int main1(){
  int pp, sg, xtc, io, dx, pv, ttdj, n8o, xl0;
  pp=50;
  sg=0;
  xtc=sg;
  io=pp;
  dx=-8;
  pv=0;
  ttdj=8;
  n8o=pp;
  xl0=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= sg <= pp;
  loop invariant xtc == sg/2;
  loop invariant xl0 == 6 + sg/2;
  loop invariant dx == -8 - ((sg + 1) / 2);
  loop invariant (sg <= 36) ==> (ttdj == 8 + sg);
  loop invariant n8o == 50 + sg*(sg+1)/2;
  loop invariant pv >= 0;
  loop invariant io == pp - (sg + 1) / 2;
  loop invariant n8o == pp + sg * (sg + 1) / 2;
  loop invariant n8o == pp + sg * (sg + 1) / 2 &&
                    xtc == sg / 2 &&
                    xl0 == 6 + sg / 2 &&
                    io == pp - (sg + 1) / 2 &&
                    dx == -8 - (sg + 1) / 2 &&
                    ttdj <= 44 &&
                    ttdj <= 8 + sg;
  loop invariant 8 <= ttdj;
  loop invariant ttdj <= 44;
  loop invariant ttdj <= pp - 6;
  loop assigns sg, xtc, xl0, io, dx, ttdj, n8o, pv;
*/
while (1) {
      if (!(sg < pp)) {
          break;
      }
      sg += 1;
      if (!(!((sg % 2) == 0))) {
          xtc += 1;
          xl0 = xl0 + 1;
      }
      else {
          io--;
          dx -= 1;
      }
      if (ttdj+6<pp) {
          ttdj = ttdj + 1;
      }
      n8o = n8o+io-io;
      pv = pv+ttdj+n8o;
      n8o += sg;
      pv += 1;
  }
}