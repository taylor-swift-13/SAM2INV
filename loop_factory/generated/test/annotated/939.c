int main1(){
  int dm, zt2, qj;
  dm=6;
  zt2=(1%20)+10;
  qj=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zt2 >= 0;
  loop invariant qj >= 0;
  loop invariant dm >= 6;
  loop invariant zt2 + qj == 26 - dm;
  loop assigns dm, zt2, qj;
*/
while (zt2>0&&qj>0) {
      if (!(!(dm%2==0))) {
          zt2--;
      }
      else {
          qj--;
      }
      dm += 1;
  }
}