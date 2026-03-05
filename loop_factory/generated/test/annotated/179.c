int main1(){
  int m, ldcz;
  m=1;
  ldcz=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 1;
  loop invariant ldcz % 2 == 1;
  loop invariant ldcz >= 1;
  loop invariant ldcz <= 2*m + 1;
  loop assigns ldcz;
*/
while (ldcz<=m) {
      ldcz = ldcz + ldcz;
      ldcz = ldcz + 1;
  }
}