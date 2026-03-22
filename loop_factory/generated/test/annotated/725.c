int main1(int z,int c){
  int kwis, nw, x1k;
  kwis=0;
  nw=(z%28)+10;
  x1k=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nw == ((\at(z,Pre) % 28) + 10) - (kwis * (kwis - 1)) / 2;
  loop invariant x1k == \at(z,Pre) + (kwis * (kwis + 1)) / 2;
  loop invariant kwis >= 0;
  loop assigns nw, kwis, x1k;
*/
while (1) {
      if (!(nw>kwis)) {
          break;
      }
      nw -= kwis;
      kwis += 1;
      x1k = (kwis)+(x1k);
  }
}