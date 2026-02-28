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
  loop invariant v >= p;
  loop invariant r <= v;

  loop invariant p == (k % 7) + 8;
  loop invariant (r == 0) || (v - r == 3);
  loop invariant ((r == 0 && v == p) || (r == v - 3));
  loop invariant (v - p) % 3 == 0;
  loop assigns r, v;
*/
while (1) {
      r = v;
      v = v+3;
  }

}
