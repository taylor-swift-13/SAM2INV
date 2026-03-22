int main1(){
  int a4o, k, x;
  a4o=1;
  k=-3173;
  x=a4o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a4o == 1;
  loop invariant x >= 1;
  loop invariant 6*k == x*x - 9*x - 19030;
  loop invariant x % 3 == 1;
  loop assigns k, x;
*/
while (k<=-1) {
      k = (k+x)+(-(3));
      x += 2;
      x = x + 1;
  }
}