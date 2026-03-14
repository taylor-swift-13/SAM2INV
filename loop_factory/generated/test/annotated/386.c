int main1(int e,int q){
  int hb, k, o, s;
  hb=q;
  k=0;
  o=3;
  s=9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hb == \at(q,Pre);
  loop invariant o == 3 + 6*k;
  loop invariant s == 9 + 6*k;
  loop invariant k >= 0;
  loop invariant (hb >= 0) ==> (k <= hb);
  loop assigns o, k, s;
*/
while (1) {
      if (!(k<=hb-1)) {
          break;
      }
      o += 6;
      k += 1;
      s += 6;
  }
}