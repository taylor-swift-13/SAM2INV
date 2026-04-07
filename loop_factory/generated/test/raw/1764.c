int main1(){
  int t6, ncq7, a3, osiq;

  t6=(1%24)+16;
  ncq7=1;
  a3=t6;
  osiq=ncq7;

  while (1) {
      if (!(ncq7*4<=t6)) {
          break;
      }
      osiq = osiq + 1;
      a3 = a3+osiq*osiq*osiq*osiq;
      t6 = (ncq7*4)-1;
  }

}
