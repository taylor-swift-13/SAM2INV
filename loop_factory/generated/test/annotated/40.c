int main1(int b,int k,int m,int n){
  int l, i, v, r;

  l=66;
  i=l;
  v=-1;
  r=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i >= 0;
   loop invariant v + i == 65;
   loop invariant r == i - 71;
   loop invariant b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
   loop invariant v == 65 - i;
   loop invariant i <= 66;
   loop invariant l == 66;
   loop invariant b == \at(b, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant n == \at(n, Pre);
   loop invariant i + v == 65;
   loop invariant v + r == -6;
   loop invariant 0 <= i && i <= 66;
   loop assigns i, v, r;
   loop variant i;
 */
while (i>0) {
      v = v+1;
      r = r-1;
      i = i-1;
  }

}