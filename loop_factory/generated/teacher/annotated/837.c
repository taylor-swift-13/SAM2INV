int main1(int a,int k,int q){
  int n, h, u, c;

  n=8;
  h=1;
  u=5;
  c=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);


  loop invariant u*u - 2*u*c - 2*c*c + u - 10*c == 30 - 20*q - 2*q*q;
  loop invariant u*u - 2*u*c - 2*c*c + u - 10*c == 30 - 20*\at(q,Pre) - 2*\at(q,Pre)*\at(q,Pre);
  loop invariant n == 8;

  loop assigns u, c;
*/
while (1) {
      u = u+2;
      c = c+u;
      u = u+c+c;
      u = u+1;
  }

}
