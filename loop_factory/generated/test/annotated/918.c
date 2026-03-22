int main1(int j,int o){
  int dsz, it, fqn, emw;
  dsz=(j%36)+15;
  it=1;
  fqn=0;
  emw=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant emw == fqn + 1;
  loop invariant dsz == (\at(j,Pre) % 36) + 15;
  loop invariant j == \at(j,Pre) + 2*(it - 1);
  loop invariant it >= 1;
  loop assigns it, emw, fqn, j;
*/
while (it<=dsz) {
      it = 2*it;
      emw += 1;
      fqn++;
      j = j + it;
  }
}