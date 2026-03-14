int main1(int r,int j){
  int fi, r0, s2j, jq2;
  fi=j;
  r0=0;
  s2j=0;
  jq2=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (s2j == 0) ==> (r0 == 0);
  loop invariant (r0 == 0) ==> (s2j == 0);
  loop invariant (r0 == 0) || (r0 == fi);
  loop invariant jq2 == \at(j, Pre) + s2j;
  loop invariant (s2j > 0) ==> (r0 == fi);
  loop invariant fi == \at(j, Pre);
  loop invariant r == \at(r, Pre) + 3*s2j;
  loop invariant 0 <= s2j <= 1;
  loop invariant s2j >= 0;
  loop assigns r, r0, s2j, jq2, j;
*/
while (1) {
      if (!(r0<=fi-1)) {
          break;
      }
      r += r0;
      s2j++;
      jq2 += 1;
      r = r + 3;
      j += r;
      r0 = fi;
  }
}