int main1(int d){
  int wip, ey, o;

  wip=24;
  ey=0;
  o=0;

  while (ey<wip) {
      o = o + 1;
      if (o>=6) {
          o -= 6;
          o = o + 1;
      }
      ey = ey + 1;
  }

}
