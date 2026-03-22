int main1(int i,int d){
  int gz, wmtv, nka;
  gz=0;
  wmtv=(i%28)+10;
  nka=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wmtv == ((\at(i,Pre) % 28) + 10) - (gz * (gz - 1)) / 2;
  loop invariant wmtv == (((i % 28) + 10) - ((gz * (gz - 1)) / 2));
  loop invariant nka  == 8 + (gz * ((i % 28) + 10)) - ((gz * (gz - 1) * (gz + 1)) / 6);
  loop invariant gz  >= 0;
  loop invariant nka >= 8;
  loop assigns wmtv, gz, nka;
*/
while (wmtv>gz) {
      wmtv = wmtv - gz;
      gz = gz + 1;
      nka = (wmtv)+(nka);
  }
}