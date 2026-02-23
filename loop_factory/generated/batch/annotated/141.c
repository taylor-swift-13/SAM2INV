int main1(int k){
  int h, o, v, r;

  h=k-9;
  o=h;
  v=h;
  r=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == k - 9;
  loop invariant v <= h;
  loop invariant k == \at(k, Pre);
  loop invariant h == \at(k, Pre) - 9;
  loop invariant \at(k, Pre) - 9 <= v;
  loop assigns v;
*/
while (v<h) {
      if (v<h) {
          v = v+1;
      }
  }

}
