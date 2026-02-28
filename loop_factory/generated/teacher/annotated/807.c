int main1(int p,int q){
  int h, k, e, v;

  h=38;
  k=3;
  e=-4;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 38;
  loop invariant k == 3;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (e + 4) % (1 + k) == 0;
  loop invariant e % 4 == 0;
  loop invariant e >= -4;
  loop invariant (e + 4) % 4 == 0;
  loop invariant (v == q + h) || (v == k);
  loop assigns v, e;
*/
while (1) {
      v = v+e;
      e = e+1;
      v = v-1;
      e = e+k;
      v = v+k;
      v = q+h;
  }

}
