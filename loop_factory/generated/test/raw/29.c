int main1(int w,int i,int h){
  int fg, d7, ab8, uo;

  fg=61;
  d7=2;
  ab8=0;
  uo=0;

  while (1) {
      if (!(uo<fg)) {
          break;
      }
      ab8 = (ab8+1)%7;
      uo = uo + 1;
      w += 2;
      h = h + d7;
  }

}
