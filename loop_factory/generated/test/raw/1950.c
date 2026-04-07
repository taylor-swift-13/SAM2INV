int main1(int f){
  int wm, ol, a5;

  wm=f*3;
  ol=0;
  a5=ol;

  while (ol < wm) {
      a5 += a5;
      f = f + 1;
      ol = ol + 1;
  }

}
