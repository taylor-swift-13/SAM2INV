int main1(int e,int a){
  int bdr, n1z;
  bdr=59;
  n1z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bdr == 59;
  loop invariant e == \at(e, Pre) + a * n1z;
  loop invariant 0 <= n1z <= bdr;
  loop assigns e, n1z;
*/
while (1) {
      e = e + a;
      n1z += 1;
      if (n1z>=bdr) {
          break;
      }
  }
}