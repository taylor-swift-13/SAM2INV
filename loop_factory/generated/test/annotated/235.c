int main1(int t,int r){
  int gpw, md;
  gpw=t;
  md=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(r,Pre);
  loop invariant md >= 0;
  loop invariant t >= \at(t,Pre);
  loop invariant (gpw != 0) ==> ((t - \at(t,Pre)) % gpw == 0);
  loop assigns md, t;
*/
while (md<=gpw) {
      md = 2*md;
      md += 1;
      t += gpw;
  }
}