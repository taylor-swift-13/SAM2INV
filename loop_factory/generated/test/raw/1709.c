int main1(int j){
  int z, pg, og, qd;

  z=j+11;
  pg=0;
  og=0;
  qd=-8;

  while (1) {
      if (!(og<=z-1)) {
          break;
      }
      if (!(!(og>=z/2))) {
          qd += 4;
      }
      j = j + pg;
      og++;
  }

}
