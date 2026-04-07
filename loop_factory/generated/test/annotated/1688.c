int main1(){
  int gi, ub, av, uc2;
  gi=1+20;
  ub=gi;
  av=0;
  uc2=ub;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant av == ub - gi;
  loop invariant uc2 >= ub;
  loop invariant ub >= gi/2;
  loop invariant uc2 == 21 + 21*av + av*(av - 1)/2;
  loop invariant uc2 == gi + gi*(ub - gi) + ((ub - gi)*(ub - gi - 1))/2;
  loop assigns av, uc2, ub;
*/
while (ub-2>=0) {
      if (ub<gi/2) {
          av += uc2;
      }
      else {
          av += 1;
      }
      uc2 = uc2 + ub;
      ub += 1;
  }
}