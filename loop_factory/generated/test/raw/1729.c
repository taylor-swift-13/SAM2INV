int main1(int v){
  int y, m, i;

  y=(v%28)+14;
  m=0;
  i=0;

  while (1) {
      if (!(m < y)) {
          break;
      }
      m++;
      i = i + 3;
      v = v + m;
      i = i + 1;
  }

}
