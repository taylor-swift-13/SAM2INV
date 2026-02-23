int main1(int b,int k){
  int m, t, i;

  m=b+3;
  t=0;
  i=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == b + 3;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant i % 2 == 0;
  loop invariant m == \at(b, Pre) + 3;

  loop invariant (t <= m) || (m <= 0);
  loop invariant t >= 0;
  loop assigns i, t;
*/
while (t<m) {
      i = i+i;
      if ((t%9)==0) {
          i = i+2;
      }
      t = t+1;
  }

}
