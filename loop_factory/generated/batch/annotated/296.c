int main1(int b,int k){
  int p, q, v, r;

  p=(k%7)+8;
  q=0;
  v=p;
  r=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant p == (\at(k, Pre) % 7) + 8;

  loop invariant p <= 14;
  loop invariant p == (k % 7) + 8;
  loop invariant v <= p;
  loop invariant r >= 0;
  loop invariant v >= 0;
  loop invariant v == p;
  loop invariant r == 0;
  loop invariant r <= p + 1;
  loop assigns v, r;
*/
while (v<p) {
      if (v<p) {
          v = v+1;
      }
      r = r+r;
      r = r+v;
      v = v+1;
      v = v+r;
      r = v-r;
  }

}
