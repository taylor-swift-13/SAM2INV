int main1(int a,int k,int p,int q){
  int m, i, x, w;

  m=(k%29)+10;
  i=0;
  x=1;
  w=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant x == 1 + 3*i;
  loop invariant w == 4;
  loop invariant m == (\at(k,Pre) % 29) + 10;
  loop invariant k == \at(k,Pre);
  loop invariant a == \at(a,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant 0 <= i;

  loop invariant m == (k % 29) + 10;
  loop assigns i, x, w;
*/
while (1) {
      if (i>=m) {
          break;
      }
      x = x+2;
      i = i+1;
      x = x+1;
      w = w-1;
      w = w+1;
  }

}
