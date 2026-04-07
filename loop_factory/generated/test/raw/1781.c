int main1(int c){
  int dl, yqbv, z, e, bb84;

  dl=0;
  yqbv=(c%60)+60;
  z=(c%9)+2;
  e=0;
  bb84=0;

  while (1) {
      if (yqbv<=z*e+bb84) {
          break;
      }
      if (bb84==z-1) {
          bb84 = 0;
          e += 1;
      }
      else {
          bb84++;
      }
      c = (dl)+(c);
  }

}
