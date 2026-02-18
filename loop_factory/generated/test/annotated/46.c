int main1(int b,int k,int m,int q){
  int l, i, v, g;

  l=31;
  i=l;
  v=q;
  g=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant -v + g + 3*i == \at(k, Pre) - \at(q, Pre) + 93;
   loop invariant b == \at(b, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant 0 <= i;
   loop invariant i <= 31;
   loop invariant l == 31;
   loop invariant i >= 0;
   loop invariant g - v + 3*i == \at(k, Pre) - \at(q, Pre) + 93;
   loop invariant 0 <= i <= 31;
   loop invariant k == \at(k,Pre);
   loop invariant b == \at(b,Pre);
   loop invariant m == \at(m,Pre);
   loop invariant q == \at(q,Pre);
   loop assigns v, g, i;
   loop variant i;
 */
while (i>0) {
      v = v+g;
      g = g+g;
      g = g+3;
      i = i-1;
  }

}