import lxml.etree as ET


class XMLStreamParser(object):
    def __init__(self, callback, *args, **kwargs):
        self._callback = callback
        self._depth = 0
        self._builder = ET.TreeBuilder()

        self._parser = ET.XMLParser(*args, target=self, **kwargs)
        self._parser.feed('<?xml version="1.0" standalone="yes" ?>')
        self._parser.feed('<!DOCTYPE coq [ <!ENTITY nbsp " "> ]>')
        self._parser.feed('<fakeroot>')

    def start(self, tag, attrs):
        self._depth += 1
        self._builder.start(tag, attrs)

    def end(self, tag):
        xml = self._builder.end(tag)

        self._depth -= 1
        if self._depth == 1:
            self._callback(xml)

    def data(self, data):
        self._builder.data(data)

    def feed(self, data):
        self._parser.feed(data)


class XmlBuilder_(object):
    def __init__(self, xml, root_xml):
        self.xml = xml
        self.root_xml = root_xml

    def done(self):
        return self.root_xml

    def add(self, tag, *args, **kwargs):
        sub = ET.Element(tag, *args, **kwargs)
        self.xml.append(sub)
        return XmlBuilder_(sub, self.root_xml)

    def text(self, s):
        self.xml.text = s
        return self

    def unit(self):
        return self.add('unit')

    def int(self, i):
        return self.add('int').text(str(i))

    def bool(self, b):
        return self.add('bool', val=str(b).lower())

    def string(self, s):
        return self.add('string').text(s)

    def state_id(self, sid):
        return self.add('state_id', val=str(sid.id))

    def none(self):
        return self.add('option', val='none')

    def some(self):
        return self.add('option', val='some')

    def pair(self):
        return self.add('pair')

def XmlBuilder(tag, *args, **kwargs):
    xml = ET.Element(tag, *args, **kwargs)
    return XmlBuilder_(xml, xml)
