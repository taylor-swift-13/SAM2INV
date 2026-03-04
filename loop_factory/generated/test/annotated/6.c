int main1(int u,int w){
  int xt, z5, ii1, a;
  xt=u+8;
  z5=xt;
  ii1=0;
  a=xt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z5 == xt;
  loop invariant u == \at(u, Pre) + ii1;
  loop invariant w == \at(w, Pre) + ii1*(ii1+1)/2;
  loop invariant 0 <= ii1;
  loop invariant (ii1 == 0 ==> a == xt);
  loop invariant (ii1 > 0 ==> a == xt - (ii1 - 1));
  loop invariant ii1 >= 0;
  loop invariant u >= \at(u, Pre);
  loop invariant w >= \at(w, Pre);
  loop invariant a <= xt;
  loop assigns a, ii1, u, w;
*/
while (1) {
      if (!(z5-3>=0)) {
          break;
      }
      a = xt-ii1;
      ii1++;
      u = u + 1;
      w = w + ii1;
  }
}