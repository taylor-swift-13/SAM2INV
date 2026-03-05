int main1(int n){
  int w, o, nob;
  w=13;
  o=0;
  nob=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre) + o*(o+1)/2;
  loop invariant (o == 0) ==> (nob == 4);
  loop invariant w == 13;
  loop invariant 0 <= o <= w;
  loop invariant 0 <= nob <= 4;
  loop assigns n, o, nob;
*/
while (o<w) {
      nob = o%5;
      if (o>=nob) {
          nob = (o-nob)%5;
          nob = nob+nob-nob;
      }
      else {
          nob = nob + nob;
      }
      o = o + 1;
      n = n + o;
  }
}