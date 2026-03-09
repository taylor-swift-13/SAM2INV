int main1(int j){
  int o3, a37, to, mu;
  o3=j+17;
  a37=0;
  to=j;
  mu=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o3 == j + 17;
  loop invariant a37 % 4 == 0;
  loop invariant mu == j + 2 * (a37/4) * ((a37/4) + 1);
  loop invariant mu == \at(j, Pre) + 2 * (a37/4) * ((a37/4) + 1);
  loop invariant a37 >= 0;
  loop assigns a37, to, mu;
*/
while (1) {
      if (!(a37<o3)) {
          break;
      }
      to = o3-a37;
      a37 += 4;
      mu = mu + a37;
  }
}