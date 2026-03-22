int main1(){
  int pt, e1fd, wz, d;

  pt=1;
  e1fd=1;
  wz=pt;
  d=-4;

  while (1) {
      if (!(e1fd < pt)) {
          break;
      }
      d = ((d%3)+1)+(d*4);
      e1fd = e1fd * 2;
      wz++;
  }

}
