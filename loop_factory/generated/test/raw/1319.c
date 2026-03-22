int main1(int u,int h){
  int cc, w3, ci, wtq, mn;

  cc=h+13;
  w3=1;
  ci=0;
  wtq=(u%28)+10;
  mn=u;

  while (wtq>ci) {
      wtq -= ci;
      mn += 2;
      ci = ci + 1;
      u = u+cc-w3;
  }

}
