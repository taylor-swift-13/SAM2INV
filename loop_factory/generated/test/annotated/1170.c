int main1(int b){
  int stn, il, ta5s, l8, man;
  stn=103;
  il=0;
  ta5s=1;
  l8=1;
  man=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ta5s == (il + 1) * (il + 1);
  loop invariant l8 == 2 * il + 1;
  loop invariant man == (3 * il * il + 5 * il - 2) / 2;
  loop invariant il >= 0;
  loop assigns il, l8, man, ta5s;
*/
while (ta5s<=stn) {
      il = il + 1;
      l8 += 2;
      man = man+l8+il;
      ta5s += l8;
  }
}