int main1(int j,int e){
  int dlb1, tz, u4o4;

  dlb1=(e%6)+19;
  tz=0;
  u4o4=e;

  while (1) {
      if (!(u4o4<dlb1)) {
          break;
      }
      if (u4o4<dlb1) {
          u4o4 += 1;
      }
      j += tz;
      e += 2;
      j = j + e;
  }

}
