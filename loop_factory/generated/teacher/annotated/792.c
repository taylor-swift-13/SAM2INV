int main1(int k,int m){
  int g, u, i, x;

  g=36;
  u=0;
  i=0;
  x=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 36;
  loop invariant 0 <= i;
  loop invariant i <= g;
  loop invariant (x % 2) == 0;
  loop invariant x % 4 == 0;
  loop invariant x >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= i <= g;
  loop invariant x >= 2*i;
  loop invariant 0 <= i && i <= g && x % 4 == 0 && (i <= g/2 ==> x >= 0);
  loop assigns i, x;
*/
while (i<g) {
      if (i<g/2) {
          x = x+2;
      }
      else {
          x = x-2;
      }
      i = i+1;
      x = x+x;
  }

}
