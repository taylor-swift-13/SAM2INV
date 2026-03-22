int main1(){
  int na4, a, pl, u;
  na4=(1%20)+1;
  a=(1%25)+1;
  pl=0;
  u=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant na4 % 2 == 0;
  loop invariant a >= 0;
  loop invariant pl >= 0;
  loop invariant u == 2 * na4 - 3;
  loop invariant na4 >= 2;
  loop assigns a, na4, pl, u;
*/
while (a!=0) {
      if (a%2==1) {
          pl = pl + na4;
          a -= 1;
      }
      else {
      }
      a = a/2;
      na4 = 2*na4;
      u = u + na4;
  }
}