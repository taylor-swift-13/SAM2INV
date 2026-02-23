int main1(int b,int k){
  int m, i, h, v;

  m=35;
  i=0;
  h=k;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 35;
  loop invariant i <= m;
  loop invariant i >= 0;
  loop invariant h == k + 2*i;
  loop invariant v == b + i*k + i*i + i;
  loop invariant v == b + i*(k+1) + i*i;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant h == \at(k, Pre) + 2*i;
  loop invariant v == \at(b, Pre) + i*(\at(k, Pre) + i + 1);
  loop invariant 0 <= i;
  loop invariant v == \at(b, Pre) + i * \at(k, Pre) + i * (i + 1);
  loop invariant v == b + i*k + i*(i+1);
  loop assigns h, v, i;
*/
while (i<m) {
      h = h+2;
      v = v+h;
      i = i+1;
  }

}
