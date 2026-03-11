int main1(int b,int n){
  int j, a, e, f;

  j=(b%11)+11;
  a=j;
  e=a;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (a>0) {
      e = e+1;
      f = f-1;
      a = a-1;
  }
/*@
  assert !(a>0) &&
         (e + f == ((b % 11) + 11) + n);
*/

}
