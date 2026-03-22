int main1(int i){
  int h, a1, mod, jt, g;

  h=i+19;
  a1=1;
  mod=a1;
  jt=a1;
  g=5;

  while (a1*2<=h) {
      jt = jt/4;
      mod = mod*4;
      g = g*3+(jt%6)+0;
      h = (a1*2)-1;
  }

}
