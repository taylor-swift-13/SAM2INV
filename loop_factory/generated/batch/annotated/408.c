int main1(int k,int m){
  int x, i, w;

  x=15;
  i=x;
  w=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant x == 15;
  loop invariant w >= 15;
  loop invariant (w - 15) % 3 == 0;
  loop invariant i <= x;
  loop invariant i == x;
  loop invariant i == 15;
  loop invariant i >= 2;
  loop invariant i <= x + 3;
  loop invariant w % 3 == 0;
  loop assigns w;
*/
while (i>=2) {
      w = w+3;
      if (i*i<=x+3) {
          w = w+i;
      }
  }

}
