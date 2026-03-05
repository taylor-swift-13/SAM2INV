int main1(int a){
  int vn7e, fu;
  vn7e=a+20;
  fu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vn7e == \at(a,Pre) + 20;
  loop invariant a >= \at(a,Pre);
  loop invariant (vn7e > 0) ==> fu <= 2*vn7e - 1;
  loop invariant fu >= 0 && (fu == 0 || fu % 2 == 1);
  loop assigns a, fu;
*/
while (fu<vn7e) {
      fu = 2*fu;
      fu = fu + 1;
      a += vn7e;
  }
}