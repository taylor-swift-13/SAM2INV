int main1(int b,int m){
  int h, n, w;

  h=79;
  n=0;
  w=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= n;
  loop invariant n <= h;
  loop invariant w <= -1;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h == 79;
  loop invariant 0 <= n <= h;
  loop invariant w <= -2;
  loop invariant (w % 2 != 0) <==> (n % 3 == 1);
  loop assigns w, n;
*/
while (n<=h-1) {
      w = w+w;
      if ((n%3)==0) {
          w = w+1;
      }
      n = n+1;
  }

}
