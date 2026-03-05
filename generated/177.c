int main177(int h){
  int b5, c, zoj, sq, fuh;

  b5=h*4;
  c=0;
  zoj=0;
  sq=0;
  fuh=0;

  while (c<b5) {
      sq = sq + 1;
      fuh += 1;
      if (sq>=6) {
          sq -= 6;
          zoj = zoj + 1;
      }
      c = c + 1;
  }

}
