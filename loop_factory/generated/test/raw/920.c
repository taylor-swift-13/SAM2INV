int main1(int e,int y){
  int pp, b7ey, u;

  pp=(y%40)+6;
  b7ey=1;
  u=0;

  while (b7ey<=pp) {
      b7ey = 2*b7ey;
      u = u + 1;
      e = e + b7ey;
      e += 1;
  }

}
