int main1(int m,int q){
  int h, s, v, k;

  h=q;
  s=0;
  v=-3;
  k=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == q;
  loop invariant s == 0;
  loop invariant k == h;
  loop invariant (v + 3) % 2 == 0;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant h == \at(q, Pre);
  loop assigns v, k;
*/
while (1) {
      v = v+4;
      v = v+k+k;
      if (s+7<=h+h) {
          k = k+s;
      }
  }

}
