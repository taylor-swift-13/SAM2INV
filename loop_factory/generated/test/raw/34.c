int main1(int p){
  int y8y, ui, kimp, s, y;

  y8y=p;
  ui=y8y;
  kimp=y8y;
  s=0;
  y=6;

  while (ui>3) {
      s = s+kimp*ui;
      kimp += ui;
      p += 2;
      y = y + s;
      ui = 3;
  }

}
