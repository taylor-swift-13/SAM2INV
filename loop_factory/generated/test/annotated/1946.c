int main1(){
  int fi, u, wg, ngd;
  fi=1-1;
  u=0;
  wg=0;
  ngd=fi;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (wg == u);
  loop invariant (ngd == fi - u);
  loop invariant (0 <= u);
  loop invariant (u <= fi);
  loop invariant (ngd + u) == fi;
  loop invariant ngd >= 0;
  loop assigns u, wg, ngd;
*/
while (u < fi) {
      u = u + 1;
      wg = u;
      ngd = fi - u;
  }
}