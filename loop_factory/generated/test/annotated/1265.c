int main1(){
  int ct, n7, vnw, zsm, u;
  ct=1;
  n7=1;
  vnw=n7;
  zsm=ct;
  u=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vnw * zsm <= 1;
  loop invariant n7 == ct;
  loop invariant ct == 1;
  loop invariant vnw >= 1;
  loop invariant (zsm == 0) || (zsm == 1);
  loop invariant u == -1;
  loop assigns vnw, zsm, u, n7;
*/
while (n7<ct) {
      vnw = vnw*4;
      zsm = zsm/4;
      u = u+(zsm%2);
      n7 = ct;
  }
}