int main1(){
  int y, ngr;

  y=-16845;
  ngr=-5;

  while (1) {
      if (!(y<=-3)) {
          break;
      }
      y = y+ngr+3;
      ngr += 2;
      ngr = ngr + 1;
  }

}
