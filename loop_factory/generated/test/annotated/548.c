int main1(int x){
  int pvfw, vj, ob, pyv;
  pvfw=x+23;
  vj=0;
  ob=0;
  pyv=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pyv == 7 - vj;
  loop invariant x == \at(x, Pre) + vj*(vj+1)/2;
  loop invariant ob == 7*vj - vj*(vj-1)/2;
  loop invariant pvfw == \at(x, Pre) + 23;
  loop invariant 0 <= vj;
  loop invariant pyv >= 0;
  loop assigns ob, pyv, vj, x;
*/
while (vj<pvfw&&pyv>0) {
      ob = ob + pyv;
      vj += 1;
      x += vj;
      pyv--;
  }
}