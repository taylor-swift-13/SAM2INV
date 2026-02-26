int main1(int n,int q){
  int y, b, v, a;

  y=(n%19)+13;
  b=0;
  v=8;
  a=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v - 8) % 3 == 0;
  loop invariant (v == 8) || (a == 2*v - 6);
  loop invariant y == (n % 19) + 13;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant ((v - 8) % 3) == 0;
  loop invariant (a == 2*(v-3)) || (a == \at(n, Pre));
  loop invariant (v >= 11) ==> (a == 2*(v - 3)) && (v - 8) % 3 == 0;
  loop invariant v >= 8;
  loop invariant (a == 2*v - 6) || (a == \at(n, Pre));
  loop assigns a, v;
*/
while (1) {
      a = v;
      v = v+3;
      a = a+a;
  }

}
