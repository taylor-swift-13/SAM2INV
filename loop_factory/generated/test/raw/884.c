int main1(int f,int y){
  int lg, h, s, ev;

  lg=42;
  h=0;
  s=0;
  ev=4;

  while (h<lg&&ev>0) {
      s = s + ev;
      h += 1;
      ev--;
      f = f + ev;
  }

}
