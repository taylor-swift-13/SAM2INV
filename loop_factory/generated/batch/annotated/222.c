int main1(int k,int m){
  int w, i, s, p;

  w=19;
  i=0;
  s=i;
  p=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 0;
  loop invariant i == 0;
  loop invariant i <= w;
  loop invariant 0 <= s;
  loop invariant s <= w;
  loop invariant s >= i;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant w == 19;
  loop invariant s >= 0;
  loop assigns s, p;
*/
while (i+3<=w) {
      if (s+1<=w) {
          s = s+1;
      }
      else {
          s = w;
      }
      p = p+p;
  }

}
