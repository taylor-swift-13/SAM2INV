int main1(int p,int u){
  int x9rg, wf, n, n0, md;
  x9rg=u;
  wf=1;
  n=4;
  n0=p;
  md=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= n;
  loop invariant md >= p;
  loop invariant (wf == 1) || (wf == x9rg);
  loop invariant (n == 4) ==> (md == \at(p,Pre) && n0 == \at(p,Pre) && wf == 1);
  loop invariant ((n == 4 && md == p && n0 == p && wf == 1) ||
                    (n == 12 && md == p + 12 && n0 == p/3 && wf == x9rg));
  loop assigns n, n0, md, wf;
*/
while (wf<x9rg) {
      n = n*3;
      n0 = n0/3;
      md += n;
      wf = x9rg;
  }
}